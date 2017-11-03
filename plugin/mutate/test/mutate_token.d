/**
Copyright: Copyright (c) 2017, Joakim Brännström. All rights reserved.
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost Software License 1.0)
Author: Joakim Brännström (joakim.brannstrom@gmx.com)
*/
module dextool_test.mutate_token;

import dextool_test.utility;

// dfmt off

@("shall mutate by dropping one off the tokens in the file")
unittest {
    mixin(EnvSetup(globalTestdir));

    makeDextool(testEnv).addInputArg(testData ~ "mutate_token/three_tokens.cpp").run;
    makeCompare(testEnv)
        .addCompare(testData ~ "mutate_token/three_tokens.cpp", "three_tokens.cpp")
        .throwOnFailure(false)
        .run
        .status
        .shouldBeFalse;
}
