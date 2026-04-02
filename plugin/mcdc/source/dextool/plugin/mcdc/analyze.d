/**
Copyright: Copyright (c) 2026, Joakim Brännström. All rights reserved.
License: MPL-2
*/
module dextool.plugin.mcdc.analyze;

import dextool.compilation_db : addSystemIncludes, defaultCompilerFilter, fileRange,
    prependFlags, parse, Compiler, CompileCommandDB;
import dextool.type : ExitStatusType, Path;
import dextool.utility : PreferLang, analyzeFile, prependDefaultFlags;
import dextool.plugin.mcdc.visitor : TUVisitor;

@safe:

ExitStatusType doAnalyze(string[] inCflags, string[] inFiles, CompileCommandDB compileDb) {
    import std.array : array;
    import std.algorithm : map;
    import std.typecons : Yes;
    import libclang_ast.context : ClangContext;

    auto compDbRange() {
        if (compileDb.empty) {
            return fileRange(inFiles.map!(a => Path(a)).array, Compiler("/usr/bin/c++"));
        }
        return compileDb.fileRange;
    }

    auto files = compDbRange.parse(defaultCompilerFilter).addSystemIncludes.prependFlags(
            prependDefaultFlags(inCflags, PreferLang.cpp)).array;

    auto exitStatus = ExitStatusType.Ok;

    foreach (pdata; files) {
        auto visitor = new TUVisitor(pdata.cmd.absoluteFile);
        auto ctx = ClangContext(Yes.prependParamSyntaxOnly);

        if (analyzeFile(pdata.cmd.absoluteFile, pdata.flags.completeFlags, visitor, ctx)
                == ExitStatusType.Errors) {
            exitStatus = ExitStatusType.Errors;
        }
    }

    return exitStatus;
}
