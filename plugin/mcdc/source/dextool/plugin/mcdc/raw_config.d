/**
Copyright: Copyright (c) 2026, Joakim Brännström. All rights reserved.
License: MPL-2
*/
module dextool.plugin.mcdc.raw_config;

import logger = std.experimental.logger;

struct RawConfiguration {
    import std.getopt : GetoptResult, getopt, defaultGetoptPrinter;

    bool help;
    bool errorHelp;
    bool shortPluginHelp;
    string[] cflags;
    string[] compileDb;
    string[] files;

    private GetoptResult helpInfo;

    void parse(string[] args) @safe {
        static import std.getopt;

        try {
            () @trusted {
                helpInfo = getopt(args, std.getopt.config.keepEndOfOptions,
                        "short-plugin-help", "short description of the plugin", &shortPluginHelp,
                        "compile-db", "Retrieve compilation parameters from the file", &compileDb,
                        "in", "Input file to parse", &files,
                        );
            }();
            help = helpInfo.helpWanted;
        } catch (std.getopt.GetOptException ex) {
            logger.error(ex.msg);
            errorHelp = true;
        }

        import std.algorithm : find;
        import std.array : array;
        import std.range : drop;

        cflags = args.find("--").drop(1).array();
    }

    void printHelp() @trusted {
        defaultGetoptPrinter("Usage: dextool mcdc [options] [--in=] [-- CFLAGS...]", helpInfo.options);
    }
}
