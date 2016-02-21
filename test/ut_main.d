//Automatically generated by unit_threaded.gen_ut_main, do not edit by hand
import std.stdio;
import unit_threaded.runner;

int main(string[] args) {
    writeln(`Running unit tests`);
    //dfmt off
    return args.runTests!(
                          "application.app",
                          "application.app_main",
                          "application.cpptestdouble",
                          "application.ctestdouble",
                          "application.types",
                          "application.utility",
                          "cpptooling.analyzer.clang.context",
                          "cpptooling.analyzer.clang.type",
                          "cpptooling.analyzer.clang.utility",
                          "cpptooling.analyzer.clang.visitor",
                          "cpptooling.analyzer.type",
                          "cpptooling.data.representation",
                          "cpptooling.data.symbol.container",
                          "cpptooling.data.symbol.typesymbol",
                          "cpptooling.generator.stub.cstub",
                          "cpptooling.generator.adapter",
                          "cpptooling.generator.classes",
                          "cpptooling.generator.cppvariant",
                          "cpptooling.generator.func",
                          "cpptooling.generator.gmock",
                          "cpptooling.generator.includes",
                          "cpptooling.utility.clang",
                          "cpptooling.utility.conv",
                          "cpptooling.utility.range",
                          "cpptooling.utility.stack",
                          "cpptooling.utility.taggedalgebraic",
                          "test.helpers"
                          );
    //dfmt on
}
