/**
Copyright: Copyright (c) 2017, Joakim Brännström. All rights reserved.
License: MPL-2
Author: Joakim Brännström (joakim.brannstrom@gmx.com)

This Source Code Form is subject to the terms of the Mozilla Public License,
v.2.0. If a copy of the MPL was not distributed with this file, You can obtain
one at http://mozilla.org/MPL/2.0/.
*/
module dextool.plugin.mutate.backend.test_mutant;

import core.time : Duration, dur;
import logger = std.experimental.logger;
import std.algorithm : map, filter, joiner, among;
import std.array : empty, array, appender;
import std.datetime : SysTime, Clock;
import std.datetime.stopwatch : StopWatch, AutoStart;
import std.exception : collectException;
import std.format : format;
import std.random : randomCover;
import std.typecons : Nullable, Tuple, Yes;

import blob_model : Blob;
import my.container.vector;
import my.fsm : Fsm, next, act, get, TypeDataMap;
import my.hash : Checksum64;
import my.named_type;
import my.optional;
import my.set;
import proc : DrainElement;
import sumtype;
static import my.fsm;

import dextool.plugin.mutate.backend.database : Database, MutationEntry,
    NextMutationEntry, spinSql, TestFile, ChecksumTestCmdOriginal;
import dextool.plugin.mutate.backend.interface_ : FilesysIO;
import dextool.plugin.mutate.backend.test_mutant.common;
import dextool.plugin.mutate.backend.test_mutant.test_cmd_runner : TestRunner,
    findExecutables, TestRunResult = TestResult;
import dextool.plugin.mutate.backend.type : Mutation, TestCase, ExitStatus;
import dextool.plugin.mutate.config;
import dextool.plugin.mutate.type : ShellCommand;
import dextool.type : AbsolutePath, ExitStatusType, Path;

@safe:

auto makeTestMutant() {
    return BuildTestMutant();
}

private:

struct BuildTestMutant {
@safe:

    import dextool.plugin.mutate.type : MutationKind;

    private struct InternalData {
        Mutation.Kind[] kinds;
        FilesysIO filesys_io;
        ConfigMutationTest config;
        ConfigSchema schemaConf;
        ConfigCoverage covConf;
    }

    private InternalData data;

    auto config(ConfigMutationTest c) @trusted nothrow {
        data.config = c;
        return this;
    }

    auto config(ConfigSchema c) @trusted nothrow {
        data.schemaConf = c;
        return this;
    }

    auto config(ConfigCoverage c) @trusted nothrow {
        data.covConf = c;
        return this;
    }

    auto mutations(MutationKind[] v) nothrow {
        import dextool.plugin.mutate.backend.mutation_type : toInternal;

        logger.infof("mutation operators: %(%s, %)", v).collectException;
        data.kinds = toInternal(v);
        return this;
    }

    ExitStatusType run(const AbsolutePath dbPath, FilesysIO fio) @trusted {
        try {
            auto db = Database.make(dbPath);
            return internalRun(db, fio);
        } catch (Exception e) {
            logger.error(e.msg).collectException;
        }

        return ExitStatusType.Errors;
    }

    private ExitStatusType internalRun(ref Database db, FilesysIO fio) {
        // trusted because the lifetime of the database is guaranteed to outlive any instances in this scope
        auto dbPtr = () @trusted { return &db; }();

        auto cleanup = new AutoCleanup;
        scope (exit)
            cleanup.cleanup;

        auto test_driver = TestDriver(dbPtr, fio, data.kinds, cleanup,
                data.config, data.covConf, data.schemaConf);

        while (test_driver.isRunning) {
            test_driver.execute;
        }

        return test_driver.status;
    }
}

struct MeasureTestDurationResult {
    bool ok;
    Duration[] runtime;
}

/** Measure the time it takes to run the test command.
 *
 * The runtime is the lowest of three executions. Anything else is assumed to
 * be variations in the system.
 *
 * If the tests fail (exit code isn't 0) any time then they are too unreliable
 * to use for mutation testing.
 *
 * Params:
 *  runner = ?
 *  samples = number of times to run the test suite
 */
MeasureTestDurationResult measureTestCommand(ref TestRunner runner, int samples) @safe nothrow {
    import std.algorithm : min;
    import proc;

    if (runner.empty) {
        collectException(logger.error("No test command(s) specified (--test-cmd)"));
        return MeasureTestDurationResult(false);
    }

    static struct Rval {
        TestRunResult result;
        Duration runtime;
    }

    auto runTest() @safe {
        auto sw = StopWatch(AutoStart.yes);
        auto res = runner.run(999.dur!"hours");
        return Rval(res, sw.peek);
    }

    static void print(TestRunResult res) @trusted {
        import std.stdio : stdout, write;

        foreach (kv; res.output.byKeyValue) {
            logger.info("test_cmd: ", kv.key);
            foreach (l; kv.value)
                write(l.byUTF8);
        }

        stdout.flush;
    }

    Duration[] runtimes;
    bool failed;
    for (int i; i < samples && !failed; ++i) {
        try {
            auto res = runTest;
            final switch (res.result.status) with (TestRunResult) {
            case Status.passed:
                runtimes ~= res.runtime;
                break;
            case Status.failed:
                goto case;
            case Status.timeout:
                goto case;
            case Status.error:
                failed = true;
                print(res.result);
                logger.info("failing commands: ", res.result.output.byKey);
                logger.info("exit status: ", res.result.exitStatus.get);
                break;
            }
            logger.infof("%s: Measured test command runtime %s", i, res.runtime);
        } catch (Exception e) {
            logger.error(e.msg).collectException;
            failed = true;
        }
    }

    return MeasureTestDurationResult(!failed, runtimes);
}

struct TestDriver {
    import std.datetime : SysTime;
    import dextool.plugin.mutate.backend.database : SchemataId, MutationStatusId;
    import dextool.plugin.mutate.backend.report.analyzers : EstimateScore;
    import dextool.plugin.mutate.backend.test_mutant.source_mutant : MutationTestDriver;
    import dextool.plugin.mutate.backend.test_mutant.timeout : calculateTimeout, TimeoutFsm;
    import dextool.plugin.mutate.type : MutationOrder;

    Database* db;
    FilesysIO filesysIO;
    Mutation.Kind[] kinds;
    AutoCleanup autoCleanup;

    ConfigMutationTest conf;
    ConfigSchema schemaConf;
    ConfigCoverage covConf;

    /// Runs the test commands.
    TestRunner runner;

    ///
    TestCaseAnalyzer testCaseAnalyzer;

    /// Stop conditions (most of them)
    TestStopCheck stopCheck;

    /// assuming that there are no more than 100 instances running in
    /// parallel.
    uint maxParallelInstances;

    // need to use 10000 because in an untested code base it is not
    // uncommon for mutants being in the thousands.
    enum long unknownWeight = 10000;
    // using a factor 1000 to make a pull request mutant very high prio
    enum long pullRequestWeight = unknownWeight * 1000;

    TimeoutFsm timeoutFsm;

    /// The time it takes to execute the test suite when no mutant is injected.
    Duration testSuiteRuntime;

    /// the next mutant to test, if there are any.
    MutationEntry nextMutant;

    // when the user manually configure the timeout it means that the
    // timeout algorithm should not be used.
    bool hardcodedTimeout;

    /// Test commands to execute.
    ShellCommand[] testCmds;

    /// mutation score estimation
    EstimateScore estimate;

    // The order to test mutants. It is either affected by the user directly or if pull request mode is activated.
    MutationOrder mutationOrder;

    static struct UpdateTimeoutData {
        long lastTimeoutIter;
    }

    static struct None {
    }

    static struct Initialize {
        bool halt;
    }

    static struct PullRequest {
    }

    static struct PullRequestData {
        import dextool.plugin.mutate.type : TestConstraint;

        TestConstraint constraint;
    }

    static struct SanityCheck {
        bool sanityCheckFailed;
    }

    static struct AnalyzeTestCmdForTestCase {
        TestCase[][ShellCommand] foundTestCases;
    }

    static struct UpdateAndResetAliveMutants {
        TestCase[][ShellCommand] foundTestCases;
    }

    static struct ResetOldMutant {
    }

    static struct ResetOldMutantData {
        /// Number of mutants that where reset.
        long maxReset;
        NamedType!(double, Tag!"OldMutantPercentage", double.init, TagStringable) resetPercentage;
    }

    static struct Cleanup {
    }

    static struct CheckMutantsLeft {
        bool allMutantsTested;
    }

    static struct SaveMutationScore {
    }

    static struct ParseStdin {
    }

    static struct PreCompileSut {
        bool compilationError;
    }

    static struct FindTestCmds {
    }

    static struct ChooseMode {
    }

    static struct MeasureTestSuite {
        bool unreliableTestSuite;
    }

    static struct MutationTest {
        NamedType!(bool, Tag!"MutationError", bool.init, TagStringable) mutationError;
        MutationTestResult[] result;
    }

    static struct MutationTestData {
        TestBinaryDb testBinaryDb;
    }

    static struct CheckTimeout {
        bool timeoutUnchanged;
    }

    static struct NextSchemataData {
        SchemataId[] schematas;
        long totalSchematas;
        long invalidSchematas;
    }

    static struct NextSchemata {
        NamedType!(bool, Tag!"HasSchema", bool.init, TagStringable, ImplicitConvertable) hasSchema;
        SchemataId schemataId;

        /// stop mutation testing because the last schema has been used and the
        /// user has configured that the testing should stop now.
        NamedType!(bool, Tag!"StopTesting", bool.init, TagStringable, ImplicitConvertable) stop;
    }

    static struct SchemataTest {
        SchemataId id;
        MutationTestResult[] result;
        bool fatalError;
    }

    static struct SchemataPruneUsed {
    }

    static struct Done {
    }

    static struct Error {
    }

    static struct UpdateTimeout {
    }

    static struct CheckPullRequestMutant {
        NamedType!(bool, Tag!"NoUnknown", bool.init, TagStringable, ImplicitConvertable) noUnknownMutantsLeft;
    }

    static struct CheckPullRequestMutantData {
        long startWorklistCnt;
        long stopAfter;
    }

    static struct NextMutant {
        NamedType!(bool, Tag!"NoUnknown", bool.init, TagStringable, ImplicitConvertable) noUnknownMutantsLeft;
    }

    static struct HandleTestResult {
        MutationTestResult[] result;
    }

    static struct CheckStopCond {
        bool halt;
    }

    static struct LoadSchematas {
    }

    static struct OverloadCheck {
        bool sleep;
    }

    static struct ContinuesCheckTestSuite {
        bool ok;
    }

    static struct ContinuesCheckTestSuiteData {
        long lastWorklistCnt;
        SysTime lastCheck;
    }

    static struct Stop {
    }

    static struct Coverage {
        bool propagate;
        bool fatalError;
    }

    static struct PropagateCoverage {
    }

    static struct ChecksumTestCmds {
    }

    static struct SaveTestBinary {
    }

    alias Fsm = my.fsm.Fsm!(None, Initialize, SanityCheck,
            AnalyzeTestCmdForTestCase, UpdateAndResetAliveMutants, ResetOldMutant,
            Cleanup, CheckMutantsLeft, PreCompileSut, MeasureTestSuite, NextMutant,
            MutationTest, HandleTestResult, CheckTimeout, Done, Error,
            UpdateTimeout, CheckStopCond, PullRequest, CheckPullRequestMutant, ParseStdin,
            FindTestCmds, ChooseMode, NextSchemata, SchemataTest, LoadSchematas,
            SchemataPruneUsed, Stop, SaveMutationScore, OverloadCheck,
            Coverage, PropagateCoverage, ContinuesCheckTestSuite,
            ChecksumTestCmds, SaveTestBinary);
    alias LocalStateDataT = Tuple!(UpdateTimeoutData, CheckPullRequestMutantData, PullRequestData,
            ResetOldMutantData, NextSchemataData, ContinuesCheckTestSuiteData, MutationTestData);

    private {
        Fsm fsm;
        TypeDataMap!(LocalStateDataT, UpdateTimeout, CheckPullRequestMutant, PullRequest,
                ResetOldMutant, NextSchemata, ContinuesCheckTestSuite, MutationTest) local;
        bool isRunning_ = true;
        bool isDone = false;
    }

    this(Database* db, FilesysIO filesysIO, Mutation.Kind[] kinds, AutoCleanup autoCleanup,
            ConfigMutationTest conf, ConfigCoverage coverage, ConfigSchema schema) {
        this.db = db;
        this.filesysIO = filesysIO;
        this.kinds = kinds;
        this.autoCleanup = autoCleanup;
        this.conf = conf;
        this.covConf = coverage;
        this.schemaConf = schema;

        this.timeoutFsm = TimeoutFsm(kinds);
        this.hardcodedTimeout = !conf.mutationTesterRuntime.isNull;
        local.get!PullRequest.constraint = conf.constraint;
        local.get!ResetOldMutant.maxReset = conf.oldMutantsNr;
        local.get!ResetOldMutant.resetPercentage = conf.oldMutantPercentage;
        this.testCmds = conf.mutationTester;
        this.mutationOrder = conf.mutationOrder;

        this.runner.useEarlyStop(conf.useEarlyTestCmdStop);
        this.runner = TestRunner.make(conf.testPoolSize);
        this.runner.useEarlyStop(conf.useEarlyTestCmdStop);
        this.runner.maxOutputCapture(
                TestRunner.MaxCaptureBytes(conf.maxTestCaseOutput.get * 1024 * 1024));
        this.runner.put(conf.mutationTester);

        // TODO: allow a user, as is for test_cmd, to specify an array of
        // external analyzers.
        this.testCaseAnalyzer = TestCaseAnalyzer(conf.mutationTestCaseBuiltin,
                conf.mutationTestCaseAnalyze, autoCleanup);

        this.stopCheck = TestStopCheck(conf);

        this.maxParallelInstances = () {
            if (mutationOrder.among(MutationOrder.random, MutationOrder.bySize))
                return 100;
            return 1;
        }();

        if (logger.globalLogLevel.among(logger.LogLevel.trace, logger.LogLevel.all))
            fsm.logger = (string s) { logger.trace(s); };
    }

    static void execute_(ref TestDriver self) @trusted {
        // see test_mutant/basis.md and figures/test_mutant_fsm.pu for a
        // graphical view of the state machine.

        self.fsm.next!((None a) => fsm(Initialize.init), (Initialize a) {
            if (a.halt)
                return fsm(CheckStopCond.init);
            return fsm(SanityCheck.init);
        }, (SanityCheck a) {
            if (a.sanityCheckFailed)
                return fsm(Error.init);
            if (self.conf.unifiedDiffFromStdin)
                return fsm(ParseStdin.init);
            return fsm(PreCompileSut.init);
        }, (ParseStdin a) => fsm(PreCompileSut.init), (AnalyzeTestCmdForTestCase a) => fsm(
                UpdateAndResetAliveMutants(a.foundTestCases)),
                (UpdateAndResetAliveMutants a) => fsm(CheckMutantsLeft.init),
                (ResetOldMutant a) => fsm(UpdateTimeout.init), (Cleanup a) {
            if (self.local.get!PullRequest.constraint.empty)
                return fsm(NextSchemata.init);
            return fsm(CheckPullRequestMutant.init);
        }, (CheckMutantsLeft a) {
            if (a.allMutantsTested && self.conf.onOldMutants == ConfigMutationTest
                .OldMutant.nothing)
                return fsm(Done.init);
            if (self.conf.testCmdChecksum.get)
                return fsm(ChecksumTestCmds.init);
            return fsm(MeasureTestSuite.init);
        }, (ChecksumTestCmds a) => MeasureTestSuite.init, (SaveMutationScore a) => SaveTestBinary.init,
                (SaveTestBinary a) => Stop.init, (PreCompileSut a) {
            if (a.compilationError)
                return fsm(Error.init);
            if (self.conf.testCommandDir.empty)
                return fsm(ChooseMode.init);
            return fsm(FindTestCmds.init);
        }, (FindTestCmds a) { return fsm(ChooseMode.init); }, (ChooseMode a) {
            if (!self.local.get!PullRequest.constraint.empty)
                return fsm(PullRequest.init);
            if (!self.conf.mutationTestCaseAnalyze.empty
                || !self.conf.mutationTestCaseBuiltin.empty)
                return fsm(AnalyzeTestCmdForTestCase.init);
            return fsm(CheckMutantsLeft.init);
        }, (PullRequest a) => fsm(CheckMutantsLeft.init), (MeasureTestSuite a) {
            if (a.unreliableTestSuite)
                return fsm(Error.init);
            if (self.covConf.use)
                return fsm(Coverage.init);
            return fsm(LoadSchematas.init);
        }, (Coverage a) {
            if (a.fatalError)
                return fsm(Error.init);
            if (a.propagate)
                return fsm(PropagateCoverage.init);
            return fsm(LoadSchematas.init);
        }, (PropagateCoverage a) => LoadSchematas.init,
                (LoadSchematas a) => fsm(ResetOldMutant.init), (CheckPullRequestMutant a) {
            if (a.noUnknownMutantsLeft)
                return fsm(Done.init);
            return fsm(NextMutant.init);
        }, (NextSchemata a) {
            if (a.hasSchema)
                return fsm(SchemataTest(a.schemataId));
            if (a.stop)
                return fsm(Done.init);
            return fsm(NextMutant.init);
        }, (SchemataTest a) {
            if (a.fatalError)
                return fsm(Error.init);
            return fsm(CheckStopCond.init);
        }, (NextMutant a) {
            if (a.noUnknownMutantsLeft)
                return fsm(CheckTimeout.init);
            return fsm(MutationTest.init);
        }, (UpdateTimeout a) => fsm(OverloadCheck.init), (OverloadCheck a) {
            if (a.sleep)
                return fsm(CheckStopCond.init);
            return fsm(ContinuesCheckTestSuite.init);
        }, (ContinuesCheckTestSuite a) {
            if (a.ok)
                return fsm(Cleanup.init);
            return fsm(Error.init);
        }, (MutationTest a) {
            if (a.mutationError)
                return fsm(Error.init);
            return fsm(HandleTestResult(a.result));
        }, (HandleTestResult a) => fsm(CheckStopCond.init), (CheckStopCond a) {
            if (a.halt)
                return fsm(Done.init);
            return fsm(UpdateTimeout.init);
        }, (CheckTimeout a) {
            if (a.timeoutUnchanged)
                return fsm(Done.init);
            return fsm(UpdateTimeout.init);
        }, (SchemataPruneUsed a) => SaveMutationScore.init,
                (Done a) => fsm(SchemataPruneUsed.init),
                (Error a) => fsm(Stop.init), (Stop a) => fsm(a));

        self.fsm.act!(self);
    }

nothrow:

    void execute() {
        try {
            execute_(this);
        } catch (Exception e) {
            logger.warning(e.msg).collectException;
        }
    }

    bool isRunning() {
        return isRunning_;
    }

    ExitStatusType status() {
        if (isDone)
            return ExitStatusType.Ok;
        return ExitStatusType.Errors;
    }

    void opCall(None data) {
    }

    void opCall(ref Initialize data) {
        logger.info("Initializing worklist").collectException;

        auto status = [Mutation.Status.unknown];
        if (!conf.useSkipMutant)
            status ~= Mutation.Status.skipped;

        spinSql!(() {
            db.worklistApi.updateWorklist(kinds, status, unknownWeight, mutationOrder);
        });

        // detect if the system is overloaded before trying to do something
        // slow such as compiling the SUT.
        if (conf.loadBehavior == ConfigMutationTest.LoadBehavior.halt && stopCheck.isHalt) {
            data.halt = true;
        }
    }

    void opCall(Stop data) {
        isRunning_ = false;
    }

    void opCall(Done data) {
        logger.info("Done!").collectException;
        isDone = true;
    }

    void opCall(Error data) {
        autoCleanup.cleanup;
    }

    void opCall(ref SanityCheck data) {
        import core.sys.posix.sys.stat : S_IWUSR;
        import std.path : buildPath;
        import my.file : getAttrs;
        import colorlog : color, Color;
        import dextool.plugin.mutate.backend.utility : checksum, Checksum;

        logger.info("Sanity check of files to mutate").collectException;

        auto failed = appender!(string[])();
        auto checksumFailed = appender!(string[])();
        auto writePermissionFailed = appender!(string[])();
        foreach (file; spinSql!(() { return db.getFiles; })) {
            auto db_checksum = spinSql!(() { return db.getFileChecksum(file); });

            try {
                auto abs_f = AbsolutePath(buildPath(filesysIO.getOutputDir, file));
                auto f_checksum = checksum(filesysIO.makeInput(abs_f).content[]);
                if (db_checksum != f_checksum) {
                    checksumFailed.put(abs_f);
                }

                uint attrs;
                if (getAttrs(abs_f, attrs)) {
                    if ((attrs & S_IWUSR) == 0) {
                        writePermissionFailed.put(abs_f);
                    }
                } else {
                    writePermissionFailed.put(abs_f);
                }
            } catch (Exception e) {
                failed.put(file);
                logger.warningf("%s: %s", file, e.msg).collectException;
            }
        }

        data.sanityCheckFailed = !failed.data.empty
            || !checksumFailed.data.empty || !writePermissionFailed.data.empty;

        if (data.sanityCheckFailed) {
            logger.info(!failed.data.empty,
                    "Unknown error when checking the files").collectException;
            foreach (f; failed.data)
                logger.info(f).collectException;

            logger.info(!checksumFailed.data.empty,
                    "Detected that file(s) has changed since last analyze where done")
                .collectException;
            logger.info(!checksumFailed.data.empty,
                    "Either restore the file(s) or rerun the analyze").collectException;
            foreach (f; checksumFailed.data)
                logger.info(f).collectException;

            logger.info(!writePermissionFailed.data.empty,
                    "Files to mutate are not writable").collectException;
            foreach (f; writePermissionFailed.data)
                logger.info(f).collectException;

            logger.info("Failed".color.fgRed).collectException;
        } else {
            logger.info("Ok".color.fgGreen).collectException;
        }
    }

    void opCall(ref OverloadCheck data) {
        if (conf.loadBehavior == ConfigMutationTest.LoadBehavior.slowdown && stopCheck.isOverloaded) {
            data.sleep = true;
            logger.info(stopCheck.overloadToString).collectException;
            stopCheck.pause;
        }
    }

    void opCall(ref ContinuesCheckTestSuite data) {
        import std.algorithm : max;
        import colorlog : color, Color;

        data.ok = true;

        if (!conf.contCheckTestSuite)
            return;

        enum forceCheckEach = 1.dur!"hours";

        const wlist = spinSql!(() => db.worklistApi.getWorklistCount);
        if (local.get!ContinuesCheckTestSuite.lastWorklistCnt == 0) {
            // first time, just initialize.
            local.get!ContinuesCheckTestSuite.lastWorklistCnt = wlist;
            local.get!ContinuesCheckTestSuite.lastCheck = Clock.currTime + forceCheckEach;
            return;
        }

        const period = conf.contCheckTestSuitePeriod.get;
        const diffCnt = local.get!ContinuesCheckTestSuite.lastWorklistCnt - wlist;
        // period == 0 is mostly for test purpose because it makes it possible
        // to force a check for every mutant.
        if (!(period == 0 || wlist % period == 0 || diffCnt >= period
                || Clock.currTime > local.get!ContinuesCheckTestSuite.lastCheck))
            return;

        logger.info("Checking the test environment").collectException;

        local.get!ContinuesCheckTestSuite.lastWorklistCnt = wlist;
        local.get!ContinuesCheckTestSuite.lastCheck = Clock.currTime + forceCheckEach;

        compile(conf.mutationCompile, conf.buildCmdTimeout, PrintCompileOnFailure(true)).match!(
                (Mutation.Status a) { data.ok = false; }, (bool success) {
            data.ok = success;
        });

        if (data.ok) {
            try {
                data.ok = measureTestCommand(runner, 1).ok;
            } catch (Exception e) {
                logger.error(e.msg).collectException;
                data.ok = false;
            }
        }

        if (data.ok) {
            logger.info("Ok".color.fgGreen).collectException;
        } else {
            logger.info("Failed".color.fgRed).collectException;
            logger.warning("Continues sanity check of the test suite has failed.").collectException;
            logger.infof("Rolling back the status of the last %s mutants to status unknown.",
                    period).collectException;
            foreach (a; spinSql!(() => db.mutantApi.getLatestMutants(kinds, max(diffCnt, period)))) {
                spinSql!(() => db.mutantApi.updateMutation(a.id,
                        Mutation.Status.unknown, ExitStatus(0), MutantTimeProfile.init));
            }
        }
    }

    void opCall(ParseStdin data) {
        import dextool.plugin.mutate.backend.diff_parser : diffFromStdin;
        import dextool.plugin.mutate.type : Line;

        try {
            auto constraint = local.get!PullRequest.constraint;
            foreach (pkv; diffFromStdin.toRange(filesysIO.getOutputDir)) {
                constraint.value[pkv.key] ~= pkv.value.toRange.map!(a => Line(a)).array;
            }
            local.get!PullRequest.constraint = constraint;
        } catch (Exception e) {
            logger.warning(e.msg).collectException;
        }
    }

    void opCall(ref AnalyzeTestCmdForTestCase data) {
        TestCase[][ShellCommand] found;
        try {
            runner.captureAll(true);
            scope (exit)
                runner.captureAll(false);

            // using an unreasonable timeout to make it possible to analyze for
            // test cases and measure the test suite.
            auto res = runTester(runner, 999.dur!"hours");

            foreach (testCmd; res.output.byKeyValue) {
                auto analyze = testCaseAnalyzer.analyze(testCmd.key, testCmd.value, Yes.allFound);

                analyze.match!((TestCaseAnalyzer.Success a) {
                    found[testCmd.key] = a.found;
                }, (TestCaseAnalyzer.Unstable a) {
                    logger.warningf("Unstable test cases found: [%-(%s, %)]", a.unstable);
                    found[testCmd.key] = a.found;
                }, (TestCaseAnalyzer.Failed a) {
                    logger.warning("The parser that analyze the output for test case(s) failed");
                });

            }

            warnIfConflictingTestCaseIdentifiers(found.byValue.joiner.array);
        } catch (Exception e) {
            logger.warning(e.msg).collectException;
        }

        data.foundTestCases = found;
    }

    void opCall(UpdateAndResetAliveMutants data) {
        import std.traits : EnumMembers;

        // the test cases before anything has potentially changed.
        auto old_tcs = spinSql!(() {
            Set!string old_tcs;
            foreach (tc; db.testCaseApi.getDetectedTestCases)
                old_tcs.add(tc.name);
            return old_tcs;
        });

        void transaction() @safe {
            final switch (conf.onRemovedTestCases) with (ConfigMutationTest.RemovedTestCases) {
            case doNothing:
                db.testCaseApi.addDetectedTestCases(data.foundTestCases.byValue.joiner.array);
                break;
            case remove:
                bool update;
                // change all mutants which, if a test case is removed, no
                // longer has a test case that kills it to unknown status
                foreach (id; db.testCaseApi.setDetectedTestCases(
                        data.foundTestCases.byValue.joiner.array)) {
                    if (!db.testCaseApi.hasTestCases(id)) {
                        update = true;
                        db.mutantApi.updateMutationStatus(id,
                                Mutation.Status.unknown, ExitStatus(0));
                    }
                }
                if (update) {
                    db.worklistApi.updateWorklist(kinds,
                            [Mutation.Status.unknown, Mutation.Status.skipped]);
                }
                break;
            }
        }

        auto found_tcs = spinSql!(() @trusted {
            auto tr = db.transaction;
            transaction();

            Set!string found_tcs;
            foreach (tc; db.testCaseApi.getDetectedTestCases)
                found_tcs.add(tc.name);

            tr.commit;
            return found_tcs;
        });

        printDroppedTestCases(old_tcs, found_tcs);

        if (hasNewTestCases(old_tcs, found_tcs)
                && conf.onNewTestCases == ConfigMutationTest.NewTestCases.resetAlive) {
            logger.info("Adding alive mutants to worklist").collectException;
            spinSql!(() {
                db.worklistApi.updateWorklist(kinds, [
                        Mutation.Status.alive, Mutation.Status.skipped,
                        // if these mutants are covered by the tests then they will be
                        // emoved from the worklist in PropagateCoverage.
                        Mutation.Status.noCoverage
                    ]);
            });
        }
    }

    void opCall(ResetOldMutant data) {
        import std.range : enumerate;
        import dextool.plugin.mutate.backend.database.type;

        void printStatus(T0)(T0 oldestMutant, SysTime newestTest, SysTime newestFile) {
            logger.info("Tests last changed ", newestTest).collectException;
            logger.info("Source code last changed ", newestFile).collectException;

            if (!oldestMutant.empty) {
                logger.info("The oldest mutant is ", oldestMutant[0].updated).collectException;
            }
        }

        if (conf.onOldMutants == ConfigMutationTest.OldMutant.nothing) {
            return;
        }
        if (spinSql!(() => db.worklistApi.getWorklistCount) != 0) {
            // do not re-test any old mutants if there are still work to do in the worklist.
            return;
        }

        const oldestMutant = spinSql!(() => db.mutantApi.getOldestMutants(kinds, 1));
        const newestTest = spinSql!(() => db.testFileApi.getNewestTestFile).orElse(
                TestFile.init).timeStamp;
        const newestFile = spinSql!(() => db.getNewestFile).orElse(SysTime.init);
        if (!oldestMutant.empty && oldestMutant[0].updated > newestTest
                && oldestMutant[0].updated > newestFile) {
            // only re-test old mutants if needed.
            logger.info("Mutation status is up to date").collectException;
            printStatus(oldestMutant, newestTest, newestFile);
            return;
        } else {
            logger.info("Mutation status is out of sync").collectException;
            printStatus(oldestMutant, newestTest, newestFile);
        }

        const long testCnt = () {
            if (local.get!ResetOldMutant.resetPercentage.get == 0.0) {
                return local.get!ResetOldMutant.maxReset;
            }

            const total = spinSql!(() => db.mutantApi.totalSrcMutants(kinds).count);
            const rval = cast(long)(1 + total * local.get!ResetOldMutant.resetPercentage.get
                    / 100.0);
            return rval;
        }();

        auto oldest = spinSql!(() => db.mutantApi.getOldestMutants(kinds, testCnt));

        logger.infof("Adding %s old mutants to worklist", oldest.length).collectException;
        spinSql!(() {
            foreach (const old; oldest.enumerate) {
                logger.infof("%s Last updated %s", old.index + 1,
                    old.value.updated).collectException;
                db.worklistApi.addToWorklist(old.value.id);
            }
        });
    }

    void opCall(Cleanup data) {
        autoCleanup.cleanup;
    }

    void opCall(ref CheckMutantsLeft data) {
        spinSql!(() { timeoutFsm.execute(*db); });

        data.allMutantsTested = timeoutFsm.output.done;

        if (timeoutFsm.output.done) {
            logger.info("All mutants are tested").collectException;
        }
    }

    void opCall(ChecksumTestCmds data) @trusted {
        import std.file : exists;
        import my.hash : Checksum64, makeCrc64Iso, checksum;
        import dextool.plugin.mutate.backend.database.type : ChecksumTestCmdOriginal;

        auto previous = spinSql!(() => db.testCmdApi.original);

        try {
            Set!Checksum64 current;

            foreach (testCmd; hashFiles(testCmds.filter!(a => !a.empty)
                    .map!(a => a.value[0]))) {
                current.add(testCmd.cs);

                if (testCmd.cs !in previous)
                    spinSql!(() => db.testCmdApi.set(testCmd.file,
                            ChecksumTestCmdOriginal(testCmd.cs)));
            }

            foreach (a; previous.setDifference(current).toRange)
                spinSql!(() => db.testCmdApi.remove(ChecksumTestCmdOriginal(a)));

            local.get!MutationTest.testBinaryDb.original = current;
        } catch (Exception e) {
            logger.warning(e.msg).collectException;
        }

        local.get!MutationTest.testBinaryDb.mutated = spinSql!(
                () @trusted => db.testCmdApi.mutated);
    }

    void opCall(SaveMutationScore data) {
        import dextool.plugin.mutate.backend.database.type : MutationScore;
        import dextool.plugin.mutate.backend.report.analyzers : reportScore;

        if (spinSql!(() => db.mutantApi.unknownSrcMutants(kinds)).count != 0)
            return;

        const score = reportScore(*db, kinds).score;

        // 10000 mutation scores is only ~80kbyte. Should be enough entries
        // without taking up unresonable amount of space.
        spinSql!(() @trusted {
            auto t = db.transaction;
            db.putMutationScore(MutationScore(Clock.currTime, typeof(MutationScore.score)(score)));
            db.trimMutationScore(10000);
            t.commit;
        });
    }

    void opCall(SaveTestBinary data) {
        if (!local.get!MutationTest.testBinaryDb.empty)
            saveTestBinaryDb(local.get!MutationTest.testBinaryDb);
    }

    void opCall(ref PreCompileSut data) {
        import proc;

        logger.info("Checking the build command").collectException;
        compile(conf.mutationCompile, conf.buildCmdTimeout, PrintCompileOnFailure(true)).match!(
                (Mutation.Status a) { data.compilationError = true; }, (bool success) {
            data.compilationError = !success;
        });
    }

    void opCall(FindTestCmds data) {
        auto cmds = appender!(ShellCommand[])();
        foreach (root; conf.testCommandDir) {
            try {
                cmds.put(findExecutables(root.AbsolutePath)
                        .map!(a => ShellCommand([a] ~ conf.testCommandDirFlag)));
            } catch (Exception e) {
                logger.warning(e.msg).collectException;
            }
        }

        if (!cmds.data.empty) {
            testCmds ~= cmds.data;
            runner.put(this.testCmds);
            logger.infof("Found test commands in %s:", conf.testCommandDir).collectException;
            foreach (c; cmds.data) {
                logger.info(c).collectException;
            }
        }
    }

    void opCall(ChooseMode data) {
    }

    void opCall(PullRequest data) {
        import std.algorithm : sort;
        import my.set;
        import dextool.plugin.mutate.backend.database : MutationStatusId;
        import dextool.plugin.mutate.backend.type : SourceLoc;

        // deterministic testing of mutants and prioritized by their size.
        mutationOrder = MutationOrder.bySize;
        maxParallelInstances = 1;

        // make sure they are unique.
        Set!MutationStatusId mutantIds;

        foreach (kv; local.get!PullRequest.constraint.value.byKeyValue) {
            const file_id = spinSql!(() => db.getFileId(kv.key));
            if (file_id.isNull) {
                logger.infof("The file %s do not exist in the database. Skipping...",
                        kv.key).collectException;
                continue;
            }

            foreach (l; kv.value) {
                auto mutants = spinSql!(() => db.mutantApi.getMutationsOnLine(kinds,
                        file_id.get, SourceLoc(l.value, 0)));

                const preCnt = mutantIds.length;
                foreach (v; mutants)
                    mutantIds.add(v);

                logger.infof(mutantIds.length - preCnt > 0, "Found %s mutant(s) to test (%s:%s)",
                        mutantIds.length - preCnt, kv.key, l.value).collectException;
            }
        }

        logger.infof(!mutantIds.empty, "Found %s mutants in the diff",
                mutantIds.length).collectException;
        spinSql!(() {
            foreach (id; mutantIds.toArray.sort)
                db.worklistApi.addToWorklist(id, pullRequestWeight, MutationOrder.bySize);
        });

        local.get!CheckPullRequestMutant.startWorklistCnt = spinSql!(
                () => db.worklistApi.getWorklistCount);
        local.get!CheckPullRequestMutant.stopAfter = mutantIds.length;

        if (mutantIds.empty) {
            logger.warning("None of the locations specified with -L exists").collectException;
            logger.info("Available files are:").collectException;
            foreach (f; spinSql!(() => db.getFiles))
                logger.info(f).collectException;
        }
    }

    void opCall(ref MeasureTestSuite data) {
        import std.algorithm : max, sum;
        import dextool.plugin.mutate.backend.database.type : TestCmdRuntime;

        if (!conf.mutationTesterRuntime.isNull) {
            testSuiteRuntime = conf.mutationTesterRuntime.get;
            return;
        }

        logger.infof("Measuring the runtime of the test command(s):\n%(%s\n%)",
                testCmds).collectException;

        auto measures = spinSql!(() => db.testCmdApi.getTestCmdRuntimes);

        const tester = () {
            try {
                return measureTestCommand(runner, max(1, cast(int)(3 - measures.length)));
            } catch (Exception e) {
                logger.error(e.msg).collectException;
                return MeasureTestDurationResult(false);
            }
        }();

        if (tester.ok) {
            measures ~= tester.runtime.map!(a => TestCmdRuntime(Clock.currTime, a)).array;
            if (measures.length > 3) {
                measures = measures[1 .. $]; // drop the oldest
            }

            auto mean = sum(measures.map!(a => a.runtime), Duration.zero) / measures.length;

            // The sampling of the test suite become too unreliable when the timeout is <1s.
            // This is a quick and dirty fix.
            // A proper fix requires an update of the sampler in runTester.
            auto t = mean < 1.dur!"seconds" ? 1.dur!"seconds" : mean;
            logger.info("Test command runtime: ", t).collectException;
            testSuiteRuntime = t;

            spinSql!(() @trusted {
                auto t = db.transaction;
                db.testCmdApi.setTestCmdRuntimes(measures);
                t.commit;
            });
        } else {
            data.unreliableTestSuite = true;
            logger.error("The test command is unreliable. It must return exit status '0' when no mutants are injected")
                .collectException;
        }
    }

    void opCall(ref MutationTest data) {
        auto runnerPtr = () @trusted { return &runner; }();
        auto testBinaryDbPtr = () @trusted {
            return &local.get!MutationTest.testBinaryDb;
        }();

        try {
            auto g = MutationTestDriver.Global(filesysIO, db, nextMutant,
                    runnerPtr, testBinaryDbPtr, conf.useSkipMutant);
            auto driver = MutationTestDriver(g,
                    MutationTestDriver.TestMutantData(!(conf.mutationTestCaseAnalyze.empty
                        && conf.mutationTestCaseBuiltin.empty),
                        conf.mutationCompile, conf.buildCmdTimeout),
                    MutationTestDriver.TestCaseAnalyzeData(&testCaseAnalyzer));

            while (driver.isRunning) {
                driver.execute();
            }

            if (driver.stopBecauseError) {
                data.mutationError.get = true;
            } else {
                data.result = driver.result;
            }
        } catch (Exception e) {
            data.mutationError.get = true;
            logger.error(e.msg).collectException;
        }
    }

    void opCall(ref CheckTimeout data) {
        data.timeoutUnchanged = hardcodedTimeout || timeoutFsm.output.done;
    }

    void opCall(UpdateTimeout) {
        spinSql!(() { timeoutFsm.execute(*db); });

        const lastIter = local.get!UpdateTimeout.lastTimeoutIter;

        if (lastIter != timeoutFsm.output.iter) {
            logger.infof("Changed the timeout from %s to %s (iteration %s)",
                    calculateTimeout(lastIter, testSuiteRuntime),
                    calculateTimeout(timeoutFsm.output.iter, testSuiteRuntime),
                    timeoutFsm.output.iter).collectException;
            local.get!UpdateTimeout.lastTimeoutIter = timeoutFsm.output.iter;
        }

        runner.timeout = calculateTimeout(timeoutFsm.output.iter, testSuiteRuntime);
    }

    void opCall(ref CheckPullRequestMutant data) {
        const left = spinSql!(() => db.worklistApi.getWorklistCount);
        data.noUnknownMutantsLeft.get = (
                local.get!CheckPullRequestMutant.startWorklistCnt - left) >= local
            .get!CheckPullRequestMutant.stopAfter;

        logger.infof(stopCheck.aliveMutants > 0, "Found %s/%s alive mutants",
                stopCheck.aliveMutants, conf.maxAlive.get).collectException;
    }

    void opCall(ref NextMutant data) {
        nextMutant = MutationEntry.init;

        auto next = spinSql!(() {
            return db.nextMutation(kinds, maxParallelInstances);
        });

        data.noUnknownMutantsLeft.get = next.st == NextMutationEntry.Status.done;

        if (!next.entry.isNull)
            nextMutant = next.entry.get;
    }

    void opCall(HandleTestResult data) {
        saveTestResult(data.result);
        if (!local.get!MutationTest.testBinaryDb.empty)
            saveTestBinaryDb(local.get!MutationTest.testBinaryDb);
    }

    void opCall(ref CheckStopCond data) {
        const halt = stopCheck.isHalt;
        data.halt = halt != TestStopCheck.HaltReason.none;

        final switch (halt) with (TestStopCheck.HaltReason) {
        case none:
            break;
        case maxRuntime:
            logger.info(stopCheck.maxRuntimeToString).collectException;
            break;
        case aliveTested:
            logger.info("Alive mutants threshold reached").collectException;
            break;
        case overloaded:
            logger.info(stopCheck.overloadToString).collectException;
            break;
        }
        logger.warning(data.halt, "Halting").collectException;
    }

    void opCall(ref NextSchemata data) {
        auto schematas = local.get!NextSchemata.schematas;

        const threshold = schemataMutantsThreshold(schemaConf.minMutantsPerSchema.get,
                local.get!NextSchemata.invalidSchematas, local.get!NextSchemata.totalSchematas);

        while (!schematas.empty && !data.hasSchema) {
            // TODO: replace with my.collection.vector
            const id = schematas[0];
            schematas = schematas[1 .. $];
            const mutants = spinSql!(() => db.schemaApi.schemataMutantsCount(id, kinds));

            logger.infof("Schema %s has %s mutants (threshold %s)", id.get,
                    mutants, threshold).collectException;

            if (mutants >= threshold) {
                data.hasSchema.get = true;
                data.schemataId = id;
                logger.infof("Use schema %s (%s/%s)", id.get, local.get!NextSchemata.totalSchematas - schematas.length,
                        local.get!NextSchemata.totalSchematas).collectException;
            }
        }

        local.get!NextSchemata.schematas = schematas;

        data.stop.get = !data.hasSchema && schemaConf.stopAfterLastSchema;
    }

    void opCall(ref SchemataTest data) {
        import dextool.plugin.mutate.backend.test_mutant.schemata;

        // only remove schemas that are of no further use.
        bool remove;
        void updateRemove(MutationTestResult[] result) {
            // only remove if there actually are any results utherwise we do
            // not know if it is a good idea to remove it.
            // same with the overload. if mutation testing is stopped because
            // of a halt command then keep the schema.
            remove = !(result.empty || stopCheck.isHalt != TestStopCheck.HaltReason.none);

            foreach (a; data.result) {
                final switch (a.status) with (Mutation.Status) {
                case skipped:
                    goto case;
                case unknown:
                    goto case;
                case equivalent:
                    goto case;
                case noCoverage:
                    goto case;
                case alive:
                    remove = false;
                    return;
                case killed:
                    goto case;
                case timeout:
                    goto case;
                case killedByCompiler:
                    break;
                }
            }
        }

        void save(MutationTestResult[] result) {
            updateRemove(result);
            saveTestResult(result);
            logger.infof(result.length > 0, "Saving %s schemata mutant results",
                    result.length).collectException;
        }

        try {
            auto driver = SchemataTestDriver(filesysIO, &runner, db, &testCaseAnalyzer, schemaConf,
                    data.id, stopCheck, kinds, conf.mutationCompile, conf.buildCmdTimeout);

            const saveResultInterval = 20.dur!"minutes";
            auto nextSave = Clock.currTime + saveResultInterval;
            while (driver.isRunning) {
                driver.execute;

                // to avoid loosing results in case of a crash etc save them
                // continuously
                if (Clock.currTime > nextSave && !driver.hasFatalError) {
                    save(driver.popResult);
                    nextSave = Clock.currTime + saveResultInterval;
                }
            }

            data.fatalError = driver.hasFatalError;

            if (driver.hasFatalError) {
                // do nothing
            } else if (driver.isInvalidSchema) {
                local.get!NextSchemata.invalidSchematas++;
            } else {
                save(driver.popResult);
            }

            if (remove) {
                spinSql!(() => db.schemaApi.markUsed(data.id));
            }

        } catch (Exception e) {
            logger.info(e.msg).collectException;
            logger.warning("Failed executing schemata ", data.id).collectException;
        }
    }

    void opCall(SchemataPruneUsed data) {
        try {
            const removed = db.schemaApi.pruneUsedSchemas;

            if (removed != 0) {
                logger.infof("Removed %s schemas from the database", removed);
                // vacuum the database because schemas take up a significant
                // amount of space.
                db.vacuum;
            }
        } catch (Exception e) {
            logger.warning(e.msg).collectException;
        }
    }

    void opCall(LoadSchematas data) {
        if (!schemaConf.use) {
            return;
        }

        auto app = appender!(SchemataId[])();
        foreach (id; spinSql!(() => db.schemaApi.getSchematas())) {
            if (spinSql!(() => db.schemaApi.schemataMutantsCount(id,
                    kinds)) >= schemataMutantsThreshold(schemaConf.minMutantsPerSchema.get, 0, 0)) {
                app.put(id);
            }
        }

        logger.trace("Found schematas: ", app.data).collectException;
        // random reorder to reduce the chance that multipe instances of
        // dextool use the same schema
        local.get!NextSchemata.schematas = app.data.randomCover.array;
        local.get!NextSchemata.totalSchematas = app.data.length;
    }

    void opCall(ref Coverage data) {
        import dextool.plugin.mutate.backend.test_mutant.coverage;

        auto tracked = spinSql!(() => db.getLatestTimeStampOfTestOrSut).orElse(SysTime.init);
        auto covTimeStamp = spinSql!(() => db.coverageApi.getCoverageTimeStamp).orElse(
                SysTime.init);

        if (tracked < covTimeStamp) {
            logger.info("Coverage information is up to date").collectException;
            return;
        } else {
            logger.infof("Coverage is out of date with SUT/tests (%s < %s)",
                    covTimeStamp, tracked).collectException;
        }

        try {
            auto driver = CoverageDriver(filesysIO, db, &runner, covConf,
                    conf.mutationCompile, conf.buildCmdTimeout);
            while (driver.isRunning) {
                driver.execute;
            }
            data.propagate = true;
            data.fatalError = driver.hasFatalError;
        } catch (Exception e) {
            logger.warning(e.msg).collectException;
            data.fatalError = true;
        }

        if (data.fatalError)
            logger.warning("Error detected when trying to gather coverage information")
                .collectException;
    }

    void opCall(PropagateCoverage data) {
        void propagate() @trusted {
            auto trans = db.transaction;

            auto noCov = db.coverageApi.getNotCoveredMutants;
            foreach (id; noCov) {
                db.mutantApi.updateMutationStatus(id, Mutation.Status.noCoverage, ExitStatus(0));
                db.worklistApi.removeFromWorklist(id);
            }

            trans.commit;
            logger.infof("Marked %s mutants as alive because they where not covered by any test",
                    noCov.length);
        }

        spinSql!(() => propagate);
    }

    void saveTestResult(MutationTestResult[] results) @safe nothrow {
        void statusUpdate(MutationTestResult result) @safe {
            import dextool.plugin.mutate.backend.test_mutant.timeout : updateMutantStatus;

            estimate.update(result.status);

            updateMutantStatus(*db, result.id, result.status,
                    result.exitStatus, timeoutFsm.output.iter);
            db.mutantApi.updateMutation(result.id, result.profile);
            db.testCaseApi.updateMutationTestCases(result.id, result.testCases);
            db.worklistApi.removeFromWorklist(result.id);

            if (result.status == Mutation.Status.alive)
                stopCheck.incrAliveMutants;
        }

        const left = spinSql!(() @trusted {
            auto t = db.transaction;
            foreach (a; results) {
                statusUpdate(a);
            }

            const left = db.worklistApi.getWorklistCount;
            t.commit;
            return left;
        });

        logger.infof("%s mutants left to test. Estimated mutation score %.3s (error %.3s)",
                left, estimate.value.get, estimate.error.get).collectException;
    }

    void saveTestBinaryDb(ref TestBinaryDb testBinaryDb) @safe nothrow {
        import dextool.plugin.mutate.backend.database.type : ChecksumTestCmdMutated;

        spinSql!(() @trusted {
            auto t = db.transaction;
            foreach (a; testBinaryDb.added.byKeyValue) {
                db.testCmdApi.add(ChecksumTestCmdMutated(a.key), a.value);
            }
            // magic number. about 10 Mbyte in the database (8+8+8)*20000
            db.testCmdApi.trimMutated(200000);
            t.commit;
        });

        testBinaryDb.clearAdded;
    }
}

private:

/** A schemata must have at least this many mutants that have the status unknown
 * for it to be cost efficient to use schemata.
 *
 * The weights dynamically adjust with how many of the schemas that has failed
 * to compile.
 *
 * Params:
 *  checkSchemata = if the user has activated check_schemata that run all test cases before the schemata is used.
 */
long schemataMutantsThreshold(const long minThreshold, const long invalidSchematas,
        const long totalSchematas) @safe pure nothrow @nogc {
    // "10" is a magic number that felt good but not too conservative. A future
    // improvement is to instead base it on the ratio between compilation time
    // and test suite execution time.
    if (totalSchematas > 0)
        return cast(long)(minThreshold + 10.0 * (
                cast(double) invalidSchematas / cast(double) totalSchematas));
    return cast(long) minThreshold;
}

/** Compare the old test cases with those that have been found this run.
 *
 * TODO: the side effect that this function print to the console is NOT good.
 */
bool hasNewTestCases(ref Set!string old_tcs, ref Set!string found_tcs) @safe nothrow {
    bool rval;

    auto new_tcs = found_tcs.setDifference(old_tcs);
    foreach (tc; new_tcs.toRange) {
        logger.info(!rval, "Found new test case(s):").collectException;
        logger.infof("%s", tc).collectException;
        rval = true;
    }

    return rval;
}

/** Compare old and new test cases to print those that have been removed.
 */
void printDroppedTestCases(ref Set!string old_tcs, ref Set!string changed_tcs) @safe nothrow {
    auto diff = old_tcs.setDifference(changed_tcs);
    auto removed = diff.toArray;

    logger.info(removed.length != 0, "Detected test cases that has been removed:").collectException;
    foreach (tc; removed) {
        logger.infof("%s", tc).collectException;
    }
}

/// Returns: true if all tests cases have unique identifiers
void warnIfConflictingTestCaseIdentifiers(TestCase[] found_tcs) @safe nothrow {
    Set!TestCase checked;
    bool conflict;

    foreach (tc; found_tcs) {
        if (checked.contains(tc)) {
            logger.info(!conflict,
                    "Found test cases that do not have global, unique identifiers")
                .collectException;
            logger.info(!conflict,
                    "This make the report of test cases that has killed zero mutants unreliable")
                .collectException;
            logger.info("%s", tc).collectException;
            conflict = true;
        }
    }
}

private:

/**
DESCRIPTION

     The getloadavg() function returns the number of processes in the system
     run queue averaged over various periods of time.  Up to nelem samples are
     retrieved and assigned to successive elements of loadavg[].  The system
     imposes a maximum of 3 samples, representing averages over the last 1, 5,
     and 15 minutes, respectively.


DIAGNOSTICS

     If the load average was unobtainable, -1 is returned; otherwise, the num-
     ber of samples actually retrieved is returned.
 */
extern (C) int getloadavg(double* loadavg, int nelem) nothrow;
