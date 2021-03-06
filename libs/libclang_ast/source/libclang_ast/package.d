/**
Copyright: Copyright (c) 2017-2021, Joakim Brännström. All rights reserved.
License: MPL-2
Author: Joakim Brännström (joakim.brannstrom@gmx.com)

This Source Code Form is subject to the terms of the Mozilla Public License,
v.2.0. If a copy of the MPL was not distributed with this file, You can obtain
one at http://mozilla.org/MPL/2.0/.
*/
module libclang_ast;

import logger = std.experimental.logger;

import colorlog;

shared static this() {
    import std.experimental.logger : LogLevel;

    make!SimpleLogger(LogLevel.warning, "libclang_ast");
}
