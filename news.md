# vNext.release

New features for dextool mutate

 * Speedup the test phase by skipping mutants inside SDL mutants. Because a SDL
   delete the code it is higly unlikely that mutants inside such a region would
   be killed. This is basically an extension of using coverage to skip mutants
   to test.
 * Automatic classification of test cases as either unique, bad or buggy. It
   hopefully makes it easier to read the test case report and *fast* find the
   interesting test case for further inspection without having to read all test
   cases in detail.
 * (html) A page with all mutants, their status etc has been added.
 * (html) Allow a user to provide additional metadata about test cases such as
   a link to the implementation and text about the test case. This is in a
   separate json file. The intention is that tools are used to extract the
   information from the implementation of the test cases.

```json
[{"name": "tc_1", "redundant": true, "text": "<p>a text with <br> html <a href=\"foo.html\">links</a>.</p>", "location": {"file": "../../tc_1.cpp", "line": 42}}]
```

Fixes for dextool mutate

 * Fix invalid scheman when a constexpr is used as a label in a case stmt.
 * Fix broken test case suggestion SQL query.
 * Fix scattered test case report. Users have reported that the information
   about test cases are spread out in the html report. This constructs an
   individual page per test case and a summary table in `index.html` for easy
   navigation.

# v3.3.0 Emerald

General

 * Fix compatibility with D language frontend 2.079.0+

New features for dextool mutate

 * The configuration file for coverage and schema is changed to allow a user to
   specify that the runtime should not be injected by the tool. The user, you,
   manually link it. This is because the automatic injection do not always work
   thus this option fixes the problem by allowing a user to change the build
   system and link with a pre-compiled version of the runtime.
 * Install static libraries of the coverage and schema runtimes. See
   README_tutorial_autotools.md for an example of how to use them.
 * Reduce which `test_cmd` are executed when the option `test_cmd_checksum` is
   activated.  This option also activate a checksum table of `test_cmd` -
   mutation status. If the checksum of the `test_cmd` match what is already
   known then that mutation status is used instead.

Fixes for dextool mutate

 * Fix labels being duplicated in scheman and thus leading to compilation errors.
 * Fix that a UTF-8 BOM lead to compilation errors. The tool now find and warn about it.
   It further detect when the source code is in something else than UTF-8 and warn.
 * Reduce memory usage by stack allocating AST nodes.
 * Fix C++17 if-statement initialization making scheman not compile.
 * Fix slow re-analyze on a large project by optimizing the sqlite schema (use indexes).
 * Fix GC-crash on long analysis. Dangling object where collected.

# v3.2.0 Topaz

New features for dextool mutate

 * Speedup execution of tests by only running those that are affected by the
   mutant when running the *slow* source code modification engine. This is done
   by saving the checksum of all `test_cmd` after `build_cmd` is executed and
   no mutant is inserted. When a mutant is later on inserted the resulting
   `test_cmd`s are compared to the unmodified. Only those that are different
   are classified as *affected* and thus need to be executed. If no `test_cmd`
   is *affected* by the inserted mutant the mutation is classified as
   equivalent. Set `test_cmd_checksum` to true to activate the feature. It is
   by default turned off.
 * Changed the default test order of mutants to `bySize` after a thorough
   testing phase. It means that the mutants are tested in random order but
   weighted by how much they affect the program (SUT). This mean that e.g.
   large *sdl* mutants will be prioritized above *aor* mutants.

Fixes for dextool mutate

 * The captured output from the test cases wasn't possible to limit which could
   lead to a memory explosion and consequential crash of the tool because it
   ran out of memory. This has now been fixed by introducing a configuration
   option (`max_test_cmd_output`) and default limit of 10 Mbyte.
 * Fix console spam when the plugin compile the software under test. The spam
   is replaced by a timestamp that is printed once every minute to indicate to
   a CI service that it is alive and to the user how long it has been
   compiling. If the compilation fail it will automatically re-start but this
   time print all output to the console for the user to understand what went
   wrong.
 * Fix lockup when there are test cases with the same name.

# v3.1.0 Drizzle

New features for dextool mutate

 * Check that all files to mutate are writable.
 * Check periodically that the test suite, without any mutants, execute OK. If
   not, rollback the last tested mutants.
 * Save what test_cmd killed a mutant. This is only activated if test case
   analyzers are used.
 * Prioritize testing of unknown mutants.
 * Check overload/halt conditions when running a schema for each mutant that is
   tested. Previously it was only done when selecting a new schema.
 * Construct larger mutant scheman. Previously they where at most one
   translation unit. Now they can span multiple translation units (e.g. *.cpp).
   This mean that each schema contain more mutants thus the overall mutation
   testing time is reduced.
 * Continuously save the result (every 20minute) the tested mutants of a
   schema. This should reduce the overall memory usage and means that if the
   schema is interrupted only the result from the last 20 minutes (at the most)
   are lost.
 * Modernize the html layout theme.
 * Prioritize mutants to test based on how much they affect the source code in
   order to quicker give actionable feedback to the user. Based on the
   assumption that a *large* mutant that survive is *important* to kill.
 * Change high interest mutants to reporting those that affect the most src
   code and has survive. Previously it was those that had survived the most
   test suite executions but this was never used by the users. The hope is that
   those that are reported as high interest are actually *useful*, interesting
   to look at and kill.
   Also allows the number of high interest mutants that are shown to be
   changed.
 * Automatically force a re-analyze of all files when a new version of the tool
   is installed and `dextool mutate analyze` is executed.
 * Automatically save the mutation score after each test run when all mutants
   are tested. This is then used to plot a trend.
 * The HTML report and console print a SyncStatus. It shows how "in sync" the
   tested mutants are with the code changes and test suite changes.
   The further apart they are the less "trustworthy" is the report. Because
   lets say the test suite is changed to now kill a mutant that is marked as
   alive.

Fixes for dextool mutate

 * Fix bugs in schema code generation such that more scheman compile.
 * Fix bug where the dependency tracking via included headers used the wrong
   path for headers included from the current directory (`#include "foo.hpp"`).
 * Fix bug where a mutant that span multiple lines in the html report is shown
   on one line. It makes it hard to read.
 * Removed delete of case branches in switch statements. The language C/C++ and
   the Clang AST make it hard to generate correct mutants and schematan. The
   effort needed to make it work in all cases is still great. It is further a
   bit unnecessary because SDL will delete individual statements in the
   branches thus well. It doesnt't really give that much to be able to delete
   whole branches.
 * Not all mutant schematan for binary operators where generated which meant
   that speedup opportunities where lost. With this fix all binary operators
   should have a schema generated for them which speeds up dcr, ror, aor mutant
   operators.
 * Fix the size of the database when schematas are saved by compressing them on
   the fly. Reduced the size up to 90% of a database.
 * Add support for C++17 structural binding in schematas.
 * Enable scheman which mutate const variables in C/C++.
 * Fix mutation of C++ lamba expressions.
 * Fix libclang bindings. The enum CXCursorKind is **not** backward or forward
   compatible. Because of this dextool now have a binding for each version it
   supports. What happend where that the analyzed AST could, if the wrong
   binding is used, contain seemingly random nodes which mean that the
   mutations where waaaay off.
 * Fix schematas inside return-statements and when a condition contain pointers.
 * Measuring the runtime of the test suite is now done multithreaded. It is too
   slow and pessimistic to do single threaded. It was previously changed to
   single threaded because the load of the host computer could vary and lead to
   falsely classify mutants as timeout. But with the feature `--load-behavior
   slowdown` this is no longer a problem. Thus changing back to multithreaded
   to speedup both the start and overall mutation testing.
 * Remove returnFalse/returnTrue mutants because they are redundant, overlap
   with normal true/false.
 * Stop generating the equivalent mutant sdl when it deletes empty scopes.

# v3.0.0 Nice Weather

This release, as the previous once, has focused on the mutation testing plugin.
The focus has been on improving the mutation testing speed for software that
have just started to write tests to those that have a full test suite with 100%
statement coverage. The road has been long but we are finally at the finish line.

New features for dextool mutate

 * Replaced `restrict` in the configuration with `include` and `exclude` to
   allow a user to both box in what to test and to selectively exclude parts.
 * Automatically run SQL vacuum on the database to reduce its size. Currently
   triggers when there is a new tool release or schematan are removed.
 * An estimation (trend) is calculated using a kalman filter which is ran over
   the historical data of when a mutant where discovered. The intention is to
   give the user a *feeling* of how the mutation score and thus test suite
   quality is trending based on the latest code changes.
 * Add an admin command to reset a mutant subtype.
 * Add an admin command to clear the worklist.
 * Allow a user to specify retest of old mutants as a percentage of the total.
   This is to allow a user to easier predict when all mutants have been
   re-tested.
 * Reduce the database size by only saving those mutants to the database that
   the user has specified.
 * Save the test suites execution time in the database to reduce the number of
   times it needs to be executed during the warmup phase of testing mutants.
 * Save the mutation testing score in the database when all mutants have been
   tested (worklist is zero).
   Use this mutation score show a bar graph of how it has changed over time.
 * Add `--load-threshold` and `--load-behavior` to easier integrate the plugin
   in Jenkins as a *good citizen* by allowing the plugin to detect when the
   build server is overloaded and either slow down or stop mutation testing.
   Mainly intended to be used for mutation testing of the `master` branch which
   should have a lower priority than pull requests.
 * Add test case stats, uniqueness and test cases to the JSON report.
 * Save the exit code of the test suite to the database. This will be used in
   the future to improve the reports because users are interested in the
   difference between them such as when the test suite SEGFAULT verses exits
   with a failure.
 * Add tracking of the test suite to allow dextool to know if old mutants need
   to be tested because the test suite have changed.
 * Use coverage information to quickly mark mutants that exists in functions
   that are never executed by the test suite as `alive`.
 * Add AORs as a simplified AOR. Instead of producing four mutants when an
   arithmetic operator is used it only produce one.
 * Add dependency tracking to reduce the number of files that need to be
   re-analysed. It is expensive to analyze modern C++ thus by tracking the
   `#include` it is possible to see exactly which files need to be analysed
   instead of as previously, always analyse every file.
 * Enable analysis of code that isn't parsed correctly by the clang frontend by
   the analysis to proceed even though there are compilation errors.

Fixes for dextool mutate

 * Fix the table sorting in the HTML report to be numerical instead of lexical.
 * Fix the mutation score constantly "resetting" because tests are added/removed.
 * Fix schemata bug for switch statements. The scheman where not equivalent to
   the source code mutants.
 * Fix bug where the admin command to stop the timeout testing didn't actually work.
 * Removed case branch delete from mutation operator DCR because it is a
   duplicate of what SDL do for case branches.
 * Fix memory usage when analysing. A pool is now used for the mutant AST where
   all nodes are allocated. The pool is then disposed as soon as it isn't
   needed.
 * Fix bug in MemFree which calls malloc_trim and GC free to reduce the heap.
 * Always interpret the build command as a shell command to execute. Reduced or
   removes the need for a `build.sh` because the most common use where just to
   change directory and call make.
 * Separately record the time it took to test a mutant as in compile and
   execute test suite time.
 * Print what is wrong in the configuration file when it fails to parse.
 * Fix SQL query for retrieving the oldest mutants by telling it to interpret
   as a datetime and not string.
 * Remove mutants that only delete whitespaces. These are obviously equivalent
   mutants thus not interesting.
 * Fix AOR mutation operator using the modulo operator when either side is a
   floating point type by not generating this type of mutants.
 * Fix bug when counting the number of mutants a test case killed. Mutants
   where duplicated.
 * Fix mutation checksum calculation which thus repaired the previously broken
   comment robustness.
 * Fix UOI negation by using double negation instead of removing `!`. This is
   because `!` changes the type to a boolean and C++ is picky about the types.

Breaking changes to dextool mutate

 * Removed the mutation operator COR and DCC.
 * Removed the deprecated `--level` for the report subcommand.
 * Remove `restrict` from the configuration file.

# v2.3.0

# v2.2.0

# v2.1.0 Camp Fire

@joakim-brannstrom joakim-brannstrom released this on 29 Mar 2020 · 684 commits to master since this release

This release is mainly a preparation of introducing mutation schemata by
refactoring the analyse phase into more steps. A side effect of this is that
mutation schematas requires the mutants to be valid. A problem that has existed
is that the mutants produced by the SDL mutation operator had a medium
probability of introducing either invalid code or undefined behaviour. This has
been handled by the refactored analyser.

New features

    Introduce profiling of the analyse and report stage. This can be used by a user to understand "why" certain operations take time.
    Print a progress message when removing orphaned mutants. This can take a long time thus this printing avoid e.g. a Jenkins timeout and helps a user not get impatient.
    Mutations that would occur inside a C/C++ macro is now removed except a small list of hard coded exceptions such as TRUE and FALSE.
    The test command runner has been able to execute the tests in parallel since the v2.0.0. It is now possible to configure it to stop execution as soon as one of the test commands signal failure. This can reduce the time it takes to test a mutant at the expense of the report of the test cases being less accurate.
    The test command runner automatically prioritize test cases to execute by how often they kill mutants. It means that it will over time execute the best test commands first.

Fixes

    speedup database access by adding indexes. How much it helps depends on the size of the database but empirical data shows between a 20-90% speedup.
    don't generate SDL mutants that remove returns in functions that has a return type other than void.
    slow down the analyse worker threads if the database thread that store the result is overloaded.
    set the mutations operators to use to "any" if the user doesn't specify an operator.
    Reset the timeout iterator to zero when a mutation operator has finished testing all its mutants. Previously the value where kept thus it created a strange timeout behaviour when switching between operators.
    Eliminate all SDL mutants that resulted in undefined behaviour.
    Eliminate useless mutants generated from the UOI mutation operator. Instead of fully implementing the academical definition of UOI it now only removes negation. This makes UOI useful because most mutants that it generates are productive.

Deprecation

    remove the COR mutation operator. It was rarely used and produced hard to understand mutants.


# v2.0.0 Continuous Flow

@joakim-brannstrom joakim-brannstrom released this on 30 Jan 2020 · 807 commits to master since this release

This release focus on improving the integration in a CI workflow.

New features:

    Speed-up mutation testing workflow by allowing the user to use a diff to direct dextool to what files to analyse and test. The diff can be from git diff.
    Allow a user to speed-up the analyze phase when saving to the database by reducing the SQLite safety settings (--fast-db-store)
    Speed-up saving the analyze result to by only saving those files that have changed.
    Speed-up the analyzer by parallelising it.
    Allow the user to specify multiple test_cmd that is executed in parallel.
    It is now possible to specify a directory test_cmd_dir which dextool will scan, after compilation, for binaries. These binaries are added as test_cmds.
    Allow a user to specify a max runtime when testing mutants. This is to be able to give "fast" feedback on a pull request.
    Add a report section which display what mutants a test case uniquely kill and those that has no unique kills.
    Allow a user to exclude files from analysis.
    The admin command group now has an option to mark mutants with a specific status. This is for the users that can't modify the source code to add // NOMUT on lines with mutants that should be ignored.
    Which mutants that are tested in a diff is deterministic (always the same over a week) to make it possible for a user to e.g. add or change test cases to kill mutants in the diff.

Breaking change:

    test_cmd, build_cmd and analyze_cmd in the configuration file now requires that the user write the path to the command. Such as ./build.sh.

Fixes:

    Only write the output from test cases to the filesystem when the user has specified an external analyze_cmd. The builtins no longer requires this temporary storage.
    A compilation_commands.json is only required when generating a report if the report contains sections which requires it.
    Repair the short term view and rename it to diff view.
    Only reset and test old mutants when there is "time left" to do so.
    Fix bug when parsing compilation_commands.json when paths contain whitespaces.
    Allow a user to Ctrl+C when running the analyze without corrupting the database.
    Fix bug where current working directory was used instead of root from the configuration file which lead to "strange behavior" when analysing files.
    NOMUT should not count as killed.
    Fix the algorithm for how the timeout is incrementally increased to allow multiple instances of dextool to better cooperate.
    Fix livelocks in the process handling when executing test commands.


# v1.3.2 Liu Stable

@joakim-brannstrom joakim-brannstrom released this on 28 Oct 2019 · 1008 commits to master since this release

Release verified to work with the lab material for the Liu course TDDD04.

# v1.3.0 Pretty Pictures

@joakim-brannstrom joakim-brannstrom released this on 17 Aug 2019 · 1076 commits to master since this release

This release focus on the mutation testing plugin and the html report that is produced.

Mutation testing features:

    Produce a tree map in the html view over the directory/files to visualize the mutation score
    Update the html view of individual files
    Enrich the view of a mutant in a file with the test cases that killed it.


# v1.2.1 Dancing Fox

@joakim-brannstrom joakim-brannstrom released this on 16 Oct 2018 · 1612 commits to master since this release

The plugin mutate has been updated to:

    reuse data between mutants that introduce the same source code change.
    gather and report statistics about individual test cases in a test suite.
        find tests that are ineffective (do not kill any mutants).
        find tests that fully overlap in their testing.

This release marks the mutate plugin as ready to use in production.

# v1.1.0 The Sad Panda

@joakim-brannstrom joakim-brannstrom released this on 21 Mar 2017 · 2986 commits to master since this release

This release introduces a new plugin architecture akin to how git operates.

Feature

    Plugins are separate executables discovered at runtime.
    C/C++ testdouble plugin. Make it easier to grep for the dextool version in generated files by always prefixing with DEXTOOL_VERSION:.
    C/C++ testdouble plugin. New magic keyword $dextool_version$ can be used in custom headers.
    GraphML plugin. Add static as typeAttr to global variables to make it easier to find globals that are NOT local to a translation unit.

Bug Fixes

    C/C++ testdouble plugin. Header files can occur multiple times in the generated #includes in the generated code.
    C/C++ testdouble plugin. Fix -h to be more consistent with 80 columns.
    GraphML plugin. Add fallback nodes to ensure a valid graphml file is generated.


# v1.0.0 The Final Push

@joakim-brannstrom joakim-brannstrom released this on 7 Mar 2017 · 3032 commits to master since this release

This release marks the stabilization of the C and C++ test double plugins.

New Features

    (Experimental) Plugin to generate a graph of the analyzed source code. Stored in the format GraphML.

New Features C/C++ Test Double plugin

    C, can initialize/reset global variables. By default they are zero initialized.
    C/C++, log how deXtool was ran to generated the test double. It makes it easier to recreate the test double.
    C/C++, injection of custom headers support replacing $file$ with the filename of the generated file.
    C/C++, allow configuration of the compilation database filtering of compiler flags
    C, allow filtering of symbols to restrict/exclude from the generated test double.

Bug Fixes

    Unable to specify multiple --file-restrict
    Wrong headers are generated in the C/C++ test double code when using multiple --in and --file-exclude
    The destination directory (--out) isn't created if it doesn't exist which results in deXtool exiting.


# v0.8.4 Minority Report

@joakim-brannstrom joakim-brannstrom released this on 28 Nov 2016 · 3194 commits to master since this release

New Features

    It is now possible to build dextool on OSX.
    Custom header support that is injected in generated files.

Bug fixes

    Fix crash on anonymous types.
    Location for a forward declared type is wrong.
    Pointer locations aren't classified as definitions.
    The USR for a parameter isn't unique when the type is a pointer.
    Incorrectly calculated paths for compilation databases.

Internal

    Logger prints the kind of location (declaration/definition)


# v0.8.3 The Boring One

@joakim-brannstrom joakim-brannstrom released this on 9 Nov 2016 · 3226 commits to master since this release

The release mostly consist of bugfixes.

Features:

    Generate a header with the dextool version.
    Enable the user to inject a header in the generated files.

Bugs:

    Fix for the fully qualified name of implicit types residing in namespaces.
    Fix how the absolute path is derived for files from a compilation database.
    Fix USR for functions and pointers.
    Fix the uniqueness of free functions in clang 3.7


# v0.8.2 Quality of Life

@joakim-brannstrom joakim-brannstrom released this on 9 Oct 2016 · 3278 commits to master since this release

For the user:

    The methods in the C++ interface of test doubles are sorted.
    The gmock macros are sorted in the generated gmocks.

For the developer:

    End of life of the compile time generated clang AST. By generating it with a script the compile time has been improved. The total test cycle on Travis has been cut by 33%.
    Fixes to the code to make it compile with 2.072-b1. The new safety improvements found potential memory bugs.


# v0.8.1 Squice

@joakim-brannstrom joakim-brannstrom released this on 6 Oct 2016 · 3310 commits to master since this release

    (fixed) Wrong type is resolved for the pointee type of a double pointer.
    (fixed) The USR of the array types element is used instead of deriving a unique for the array.


# v0.8.0 Doing the needful

@joakim-brannstrom joakim-brannstrom released this on 12 Sep 2016 · 3327 commits to master since this release

Mostly internal refactoring to improve maintainability.

Fixes

    The definition of a symbol is used when filtering with --file-exclude or --file-restrict.
    Fix bugs when determining the location of a function that uses a typedef for the signature.
    Fix accidental merge of pointer types.


# v0.7.0 Almost Useful

@joakim-brannstrom joakim-brannstrom released this on 6 Jul 2016 · 3543 commits to master since this release

The user facing features are:

    support for compilation database (see clang). Multiple databases can be specified.
    analyze of multiple files when generating a C test double.
    improved UML diagrams.
    Better tracking of symbol location.
    Besides the plantuml diagram a pure Graphviz/dot diagram is generated.
    Identify and classify abstract classes.
    Analyze parameter dependency of free functions for component diagrams.
    etc...

Besides the new features a ton of bugs have been fixed.
Major internal refactoring.

# v0.6.0 Plugging plugins

@joakim-brannstrom joakim-brannstrom released this on 25 Feb 2016 · 3862 commits to master since this release

A plugin architecture is added to allow users to extend deXtool.

# v0.5.1 Smashing bugs

@joakim-brannstrom joakim-brannstrom released this on 22 Feb 2016 · 3871 commits to master since this release

Bugs, bugs they all exist.
Scatter, run, hide they can.
Hunt, smash, crush with wit!

Fixing bugs, no new features.
See pull requests and commits.


# v0.5.0: Merge pull request #52 from joakim-brannstrom/fix-test-compile-params

@joakim-brannstrom joakim-brannstrom released this on 21 Feb 2016 · 3879 commits to master since this release

    Relicensed under MPL-2.
    Generate correct test doubles for classes that are part of an inherit hierarchy.
    First steps take for a plugin architecture.
    Implement a workaround for generated gmocks with more than 10 parameters.
    Always generate a virtual destructor of gmocks.

etc... See git history.
