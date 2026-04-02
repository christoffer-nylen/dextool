/**
Copyright: Copyright (c) 2026, Joakim Brännström. All rights reserved.
License: MPL-2
*/
module dextool.plugin.runner;

import dextool.type : ExitStatusType;

ExitStatusType runPlugin(string[] args) @safe {
    import std.stdio : writeln;
    import dextool.compilation_db : CompileCommandDB, fromArgCompileDb;
    import dextool.plugin.mcdc.analyze : doAnalyze;
    import dextool.plugin.mcdc.raw_config : RawConfiguration;

    RawConfiguration pargs;
    pargs.parse(args);

    if (pargs.shortPluginHelp) {
        writeln("mcdc");
        writeln("print logical expressions found in c/c++ source code");
        return ExitStatusType.Ok;
    } else if (pargs.errorHelp) {
        pargs.printHelp;
        return ExitStatusType.Errors;
    } else if (pargs.help) {
        pargs.printHelp;
        return ExitStatusType.Ok;
    } else if (pargs.files.length == 0 && pargs.compileDb.length == 0) {
        writeln("Missing required argument --in or --compile-db");
        return ExitStatusType.Errors;
    }

    CompileCommandDB compileDb;
    if (pargs.compileDb.length != 0) {
        compileDb = () @trusted { return pargs.compileDb.fromArgCompileDb; }();
    }

    return doAnalyze(pargs.cflags, pargs.files, compileDb);
}
