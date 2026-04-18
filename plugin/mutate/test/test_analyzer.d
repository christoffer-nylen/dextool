/**
Copyright: Copyright (c) 2017, Joakim Brännström. All rights reserved.
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost Software License 1.0)
Author: Joakim Brännström (joakim.brannstrom@gmx.com)
*/
module dextool_test.test_analyzer;

import std.file : copy, mkdirRecurse;
import std.format : format;
import std.path : absolutePath, relativePath, buildPath;
import std.stdio : File;

import dextool.plugin.mutate.backend.database.standalone;
import dextool.plugin.mutate.backend.database.type;
import dextool.plugin.mutate.backend.type;
static import dextool.type;

import dextool_test.utility;

private enum fmtAnalyzeHangFiles = [
    "src/format.cc",
    "include/fmt/format-inl.h",
    "include/fmt/format.h",
    "include/fmt/core.h",
];

private void stageFmtAnalyzeHangSample(const ref TestEnv testEnv) {
    foreach (dir; [
            "src",
            "include/fmt",
            "build/test",
            "test/gtest"
        ]) {
        mkdirRecurse((testEnv.outdir ~ dir).toString);
    }

    foreach (relPath; fmtAnalyzeHangFiles) {
        copy((testData ~ buildPath("fmt_analyze_hang", relPath)).toString,
                (testEnv.outdir ~ relPath).toString);
    }
}

private void writeFmtAnalyzeCompileDb(const ref TestEnv testEnv, string name, bool posixMockVariant) {
    const root = absolutePath(testEnv.outdir.toString);
    const src = buildPath(root, "src", "format.cc");

    const directory = posixMockVariant
        ? buildPath(root, "build", "test")
        : buildPath(root, "build");
    const command = posixMockVariant
        ? format("/usr/bin/c++ -DFMT_LOCALE -DGTEST_HAS_STD_WSTRING=1 -D_SILENCE_TR1_NAMESPACE_DEPRECATION_WARNING=1 -I%s -isystem %s -O3 -DNDEBUG -std=gnu++11 -o CMakeFiles/posix-mock-test.dir/__/src/format.cc.o -c %s",
                buildPath(root, "include"), buildPath(root, "test", "gtest"), src)
        : format("/usr/bin/c++ -DFMT_LOCALE -I%s -O3 -DNDEBUG -std=gnu++11 -o CMakeFiles/fmt.dir/src/format.cc.o -c %s",
                buildPath(root, "include"), src);
    const output = posixMockVariant
        ? "test/CMakeFiles/posix-mock-test.dir/__/src/format.cc.o"
        : "CMakeFiles/fmt.dir/src/format.cc.o";

    File((testEnv.outdir ~ name).toString, "w").write(format(`[
  {
    "directory": "%s",
    "command": "%s",
    "file": "%s",
    "output": "%s"
  }
]
`, directory, command, src, output));
}

private auto runFmtAnalyzeWithTimeout(const ref TestEnv testEnv, string compileDb) {
    const root = absolutePath(testEnv.outdir.toString);

    return makeCommand("/usr/bin/timeout")
        .setWorkdir(testEnv.outdir)
        .throwOnExitStatus(false)
        .addArg("45s")
        .addArg(testEnv.dextool.toString)
        .addArg("mutate")
        .addArg("analyze")
        .addArg("--profile")
        .addArg("--out")
        .addArg(root)
        .addArg("--db")
        .addArg(buildPath(root, defaultDb))
        .addArg("--fast-db-store")
        .addArg("--compile-db")
        .addArg(buildPath(root, compileDb))
        .addArg("--threads")
        .addArg("1")
        .addArg("--mutant")
        .addArg("lcr")
        .run;
}

// dfmt off

@(testId ~ "shall analyze the provided file")
unittest {
    mixin(EnvSetup(globalTestdir));
    makeDextoolAnalyze(testEnv)
        .addInputArg(testData ~ "all_kinds_of_abs_mutation_points.cpp")
        .run;
}

@(testId ~ "shall exclude files from the analysis they are part of an excluded directory tree when analysing")
unittest {
    mixin(EnvSetup(globalTestdir));

    const programFile1 = testData ~ "analyze/file1.cpp";
    const programFile2 = testData ~ "analyze/exclude/file2.cpp";

    makeDextoolAnalyze(testEnv)
        .addInputArg(programFile1)
        .addInputArg(programFile2)
        .addPostArg(["--file-include", buildPath(testData.toString, "analyze/*")])
        .addPostArg(["--file-exclude", buildPath(testData.toString, "analyze/exclude/*")])
        .run;

    // assert
    auto db = Database.make((testEnv.outdir ~ defaultDb).toString);

    const file1 = dextool.type.Path(relativePath(programFile1.toString, workDir.toString));
    const file2 = dextool.type.Path(relativePath(programFile2.toString, workDir.toString));

    db.getFileId(file1).isNull.shouldBeFalse;
    db.getFileId(file2).isNull.shouldBeTrue;
}

@(testId ~ "shall analyze the provided file and use fast database storage")
unittest {
    mixin(EnvSetup(globalTestdir));
    makeDextoolAnalyze(testEnv)
        .addInputArg(testData ~ "all_kinds_of_abs_mutation_points.cpp")
        .run;
}

@(testId ~ "shall drop the unproductive mutants when analyzing")
unittest {
    mixin(EnvSetup(globalTestdir));
    auto r = makeDextoolAnalyze(testEnv)
        .addInputArg(testData ~ "unproductive_mutants.cpp")
        .addFlag("-std=c++11")
        .run;

    testAnyOrder!Re([
        `.*4.*dcrTrue`,
        `.*10.*dcrFalse`,
    ]).shouldBeIn(r.output);
}

@(testId ~ "shall drop equivalent zero-valued integer literal mutants when analyzing")
unittest {
    import std.algorithm : filter, map;
    import std.algorithm.sorting : sort;
    import std.array : array;
    import std.file : readText;
    import std.json : parseJSON;
    import std.range : iota;
    mixin(EnvSetup(globalTestdir));

    makeDextoolAnalyze(testEnv)
        .addInputArg(testData ~ "undesired_zero_integer_literals.cpp")
        .addArg(["--mutant", "cr"])
        .addFlag("-std=c++14")
        .run;

    makeDextoolReport(testEnv, testData.dirName)
        .addArg(["--style", "json"])
        .addArg(["--section", "all_mut"])
        .addArg(["--logdir", testEnv.outdir.toString])
        .run;

    const fileReports = parseJSON(readText((testEnv.outdir ~ "report.json").toString))["files"].array;

    fileReports.length.shouldEqual(1);

    const expectedCrZeroIntLines = iota(3L, 19L).array;
    auto actualCrZeroIntLines = fileReports[0]["mutants"].array
        .filter!(a => a["kind"].str == "crZeroInt")
        .map!(a => a["line"].integer)
        .array
        .sort;

    actualCrZeroIntLines.shouldEqual(expectedCrZeroIntLines);
}

@(testId ~ "shall drop equivalent zero-valued floating-point literal mutants when analyzing")
unittest {
    import std.algorithm : filter, map;
    import std.algorithm.sorting : sort;
    import std.array : array;
    import std.file : readText;
    import std.json : parseJSON;
    import std.range : iota;
    mixin(EnvSetup(globalTestdir));

    makeDextoolAnalyze(testEnv)
        .addInputArg(testData ~ "undesired_zero_float_literals.cpp")
        .addArg(["--mutant", "cr"])
        .addFlag("-std=c++14")
        .run;

    makeDextoolReport(testEnv, testData.dirName)
        .addArg(["--style", "json"])
        .addArg(["--section", "all_mut"])
        .addArg(["--logdir", testEnv.outdir.toString])
        .run;

    const fileReports = parseJSON(readText((testEnv.outdir ~ "report.json").toString))["files"].array;

    fileReports.length.shouldEqual(1);

    const expectedCrZeroFloatLines = iota(3L, 12L).array;
    auto actualCrZeroFloatLines = fileReports[0]["mutants"].array
        .filter!(a => a["kind"].str == "crZeroFloat")
        .map!(a => a["line"].integer)
        .array
        .sort;

    actualCrZeroFloatLines.shouldEqual(expectedCrZeroFloatLines);
}

@(testId ~ "shall detect changes in dependencies based on #include")
unittest {
    mixin(EnvSetup(globalTestdir));

    const programHdr = (testEnv.outdir ~ "program.hpp").toString;
    const programCpp = (testEnv.outdir ~ "program.cpp").toString;

    copy((testData ~ "analyze_dep.cpp").toString, programCpp);

    makeDextoolAnalyze(testEnv)
        .addInputArg(programCpp)
        .run;

    makeDextoolAnalyze(testEnv)
        .addInputArg(programCpp)
        .run;

    makeDextoolAnalyze(testEnv)
        .addInputArg(programCpp)
        .addFlag("-DIS_VERSION_TWO")
        .run;
}

@(testId ~ "shall transitively detect changes in dependencies")
unittest {
    import std.stdio : File;

    mixin(EnvSetup(globalTestdir));

    const programHdr = (testEnv.outdir ~ "program.hpp").toString;
    const programHdr2 = (testEnv.outdir ~ "program2.hpp").toString;
    const programCpp = (testEnv.outdir ~ "program.cpp").toString;

    copy((testData ~ "analyze_trans_dep.cpp").toString, programCpp);
    copy((testData ~ "analyze_trans_dep.hpp").toString, programHdr);
    copy((testData ~ "analyze_trans_dep2.hpp").toString, programHdr2);

    makeDextoolAnalyze(testEnv)
        .addInputArg(programCpp)
        .run;
}

@(testId ~ "shall find the mutants even though the SUT contains a compilation error")
unittest {
    mixin(EnvSetup(globalTestdir));
    auto r = makeDextoolAnalyze(testEnv)
        .addInputArg(testData ~ "analyze_compile_error.cpp")
        .addPostArg("--allow-errors")
        .run;

    testConsecutiveSparseOrder!Re(["info: Saving.*analyze_compile_error.cpp"]).shouldBeIn(r.output);
}

@(testId ~ "shall not drop mutants when analyzing with different -D")
unittest {
    mixin(EnvSetup(globalTestdir));

    copy((testData ~ "id_gen_algo/program.cpp").toString, (testEnv.outdir ~ "program.cpp").toString);
    copy((testData ~ "id_gen_algo/compile_commands.json").toString, (testEnv.outdir ~ "compile_commands.json").toString);

    auto r1 = makeDextoolAnalyze(testEnv)
        .addPostArg(["--compile-db", (testEnv.outdir ~ "compile_commands.json").toString])
        .addPostArg(["--id-algorithm", "relaxed"])
        .addPostArg(["--threads", "1"])
        .run;

    testConsecutiveSparseOrder!Re(["info: Removing orphaned.*"]).shouldBeIn(r1.output);
    testConsecutiveSparseOrder!Re(["info: Removing orphaned.*",
                                  "info: .*/.* removed.*"
    ]).shouldNotBeIn(r1.output);
}

@(testId ~ "shall finish analyze for the fmt compile command")
unittest {
    mixin(EnvSetup(globalTestdir));

    stageFmtAnalyzeHangSample(testEnv);
    writeFmtAnalyzeCompileDb(testEnv, "compile_commands_entry1.json", false);

    auto r = runFmtAnalyzeWithTimeout(testEnv, "compile_commands_entry1.json");

    r.status.shouldEqual(0);
    testConsecutiveSparseOrder!Re(["info: Analyzed 1/1 .*src/format.cc"]).shouldBeIn(r.output);
}

@(testId ~ "shall finish analyze for the fmt posix mock compile command")
unittest {
    mixin(EnvSetup(globalTestdir));

    stageFmtAnalyzeHangSample(testEnv);
    writeFmtAnalyzeCompileDb(testEnv, "compile_commands_entry2.json", true);

    auto r = runFmtAnalyzeWithTimeout(testEnv, "compile_commands_entry2.json");

    r.status.shouldEqual(0);
    testConsecutiveSparseOrder!Re(["info: Analyzed 1/1 .*src/format.cc"]).shouldBeIn(r.output);
}

@(testId ~ "shall honor a requested analyzer thread count")
unittest {
    mixin(EnvSetup(globalTestdir));

    auto r = makeDextoolAnalyze(testEnv)
        .addInputArg(testData ~ "all_kinds_of_abs_mutation_points.cpp")
        .addPostArg(["--threads", "1"])
        .addPostArg(["--verbose-module", "analyze=trace"])
        .run;

    testConsecutiveSparseOrder!Re([`trace: Using 1 analyzer worker\(s\)`]).shouldBeIn(r.output);
}
