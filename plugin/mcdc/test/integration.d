/**
Copyright: Copyright (c) 2026, Joakim Brännström. All rights reserved.
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost Software License 1.0)
*/
module dextool_test.integration;

import unit_threaded : shouldBeTrue;

import dextool_test;

enum globalTestdir = "mcdc_tests";

auto testData() {
    return Path("plugin_testdata");
}

auto makeDextool(const ref TestEnv testEnv) {
    return dextool_test.makeDextool(testEnv).args(["mcdc"]);
}

@(testId ~ "shall print logical expressions from the input file")
unittest {
    mixin(envSetup(globalTestdir));

    auto r = makeDextool(testEnv)
        .addInputArg(testData ~ "logical_expr.cpp")
        .run;

    r.output.sliceContains("a && b").shouldBeTrue;
    r.output.sliceContains("a && b || ! c").shouldBeTrue;
    r.output.sliceContains("! c").shouldBeTrue;
    r.output.sliceContains("ready || enabled").shouldBeTrue;
}
