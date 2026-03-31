/**
Copyright: Copyright (c) 2020, Joakim Brännström. All rights reserved.
License: MPL-2
Author: Joakim Brännström (joakim.brannstrom@gmx.com)

This Source Code Form is subject to the terms of the Mozilla Public License,
v.2.0. If a copy of the MPL was not distributed with this file, You can obtain
one at http://mozilla.org/MPL/2.0/.

Filter mutants based on simple textual pattern matching. These are the obvious
equivalent or undesired mutants.
*/
module dextool.plugin.mutate.backend.analyze.pass_filter;

import logger = std.experimental.logger;
import std.algorithm : among, map, filter, cache;
import std.array : appender, empty;
import std.typecons : Tuple;

import blob_model : Blob;

static import colorlog;

import dextool.plugin.mutate.backend.interface_ : FilesysIO;
import dextool.plugin.mutate.backend.type : Language, Offset, Mutation;
import dextool.plugin.mutate.backend.analyze.pass_mutant : MutantsResult;
import dextool.plugin.mutate.backend.generate_mutant : makeMutationText, MakeMutationTextResult;

alias log = colorlog.log!"analyze.pass_filter";

shared static this() {
    colorlog.make!(colorlog.SimpleLogger)(logger.LogLevel.info, "analyze.pass_filter");
}

@safe:

MutantsResult filterMutants(FilesysIO fio, MutantsResult mutants) {
    foreach (f; mutants.files.map!(a => a.path)) {
        log.trace(f);
        auto file = fio.makeInput(f);
        foreach (r; mutants.getMutationPoints(f)
                .map!(a => analyzeForUndesiredMutant(file, a, mutants.lang))
                .cache
                .filter!(a => !a.kind.empty)) {
            foreach (k; r.kind) {
                mutants.drop(f, r.point, k);
            }
        }
    }

    return mutants;
}

private:

alias Mutants = Tuple!(Mutation.Kind[], "kind", MutantsResult.MutationPoint, "point");

/// Returns: mutants to drop from the mutation point.
Mutants analyzeForUndesiredMutant(Blob file, Mutants mutants, const Language lang) {
    auto app = appender!(Mutation.Kind[])();

    foreach (k; mutants.kind) {
        if (isEmpty(file, mutants.point.offset)) {
            log.tracef("Dropping undesired mutant. Mutant is empty (%s %s %s)",
                    file.uri, mutants.point, k);
            app.put(k);
            continue;
        }

        auto mutant = makeMutationText(file, mutants.point.offset, k, lang);
        if (isTextuallyEqual(file, mutants.point.offset, mutant.rawMutation)) {
            log.tracef("Dropping undesired mutant. Original and mutant is textually equivalent (%s %s %s)",
                    file.uri, mutants.point, k);
            app.put(k);
        } else if (lang.among(Language.assumeCpp, Language.cpp)
                && isUndesiredCppPattern(file, mutants.point.offset, mutant.rawMutation)) {
            log.tracef("Dropping undesired mutant. The mutant is an undesired C++ mutant pattern (%s %s %s)",
                    file.uri, mutants.point, k);
            app.put(k);
        } else if (isOnlyWhitespace(file, mutants.point.offset, mutant.rawMutation)) {
            log.tracef("Dropping undesired mutant. Both the original and the mutant is only whitespaces (%s %s %s)",
                    file.uri, mutants.point, k);
            app.put(k);
        }
    }

    return Mutants(app.data, mutants.point);
}

bool isEmpty(Blob file, Offset o) {
    // well an empty region can just be removed
    return o.isZero || o.end > file.content.length;
}

bool isTextuallyEqual(Blob file, Offset o, const(ubyte)[] mutant) {
    return file.content[o.begin .. o.end] == mutant;
}

// if both the original and mutation is only whitespace
bool isOnlyWhitespace(Blob file, Offset o, const(ubyte)[] mutant) {
    import std.algorithm : canFind;

    static immutable ubyte[6] whitespace = [
        cast(ubyte) ' ', cast(ubyte) '\t', cast(ubyte) '\v', cast(ubyte) '\r',
        cast(ubyte) '\n', cast(ubyte) '\f'
    ];

    bool rval = true;
    foreach (a; file.content[o.begin .. o.end]) {
        rval = rval && whitespace[].canFind(a);
    }

    foreach (a; mutant) {
        rval = rval && whitespace[].canFind(a);
    }

    return rval;
}

bool isUndesiredCppPattern(Blob file, Offset o, const(ubyte)[] mutant) {
    static immutable ubyte[2] ctorParenthesis = ['(', ')'];
    static immutable ubyte[2] ctorCurly = ['{', '}'];
    static immutable ubyte zero = '0';
    static immutable ubyte one = '1';
    static immutable ubyte[5] false_ = ['f', 'a', 'l', 's', 'e'];
    static immutable ubyte[4] true_ = ['t', 'r', 'u', 'e'];

    // e.g. delete of the constructor {} is undesired. It is almost always an
    // equivalent mutant.
    if (o.end - o.begin == 2 && file.content[o.begin .. o.end].among(ctorParenthesis[],
            ctorCurly[])) {
        return true;
    }

    // replacing '0' with 'false' and '1' with 'true' is equivalent
    if (file.content[o.begin] == zero && false_ == mutant
            || file.content[o.begin] == one && true_ == mutant) {
        return true;
    }

    // replacing zero-valued integer literals with plain '0' is equivalent.
    if (isEquivalentZeroMutant(file.content[o.begin .. o.end], mutant)) {
        return true;
    }

    return false;
}

bool isEquivalentZeroMutant(const(ubyte)[] original, const(ubyte)[] mutant) {
    static immutable ubyte[][] integerLiteralSuffixes = [
        ['u'], ['U'],
        ['l'], ['L'],
        ['l', 'l'], ['L', 'L'],
        ['u', 'l'], ['u', 'L'], ['U', 'l'], ['U', 'L'], ['l', 'u'], ['l', 'U'], ['L', 'u'],
        ['L', 'U'],
        ['u', 'l', 'l'], ['u', 'L', 'L'], ['U', 'l', 'l'], ['U', 'L', 'L'], ['l', 'l', 'u'],
        ['l', 'l', 'U'], ['L', 'L', 'u'], ['L', 'L', 'U'],
        ['u', 'z'], ['u', 'Z'], ['U', 'z'], ['U', 'Z'], ['z', 'u'], ['z', 'U'], ['Z', 'u'],
        ['Z', 'U'],
        ['z'], ['Z']
    ];

    if (original.length < 2 || mutant != ['0']) {
        return false;
    }

    foreach (suffix; integerLiteralSuffixes) {
        if (!endsWith(original, suffix))
            continue;

        const literalPart = original[0 .. $ - suffix.length];
        if (isZeroIntegerLiteral(literalPart)) {
            return true;
        }
    }

    // Also filter unsuffixed zero literals such as 0x0 -> 0 and 00 -> 0.
    if (isZeroIntegerLiteral(original)) {
        return true;
    }

    return false;
}

bool endsWith(const(ubyte)[] value, const(ubyte)[] suffix) {
    if (suffix.length > value.length) {
        return false;
    }

    const start = value.length - suffix.length;
    foreach (i, s; suffix) {
        if (value[start + i] != s) {
            return false;
        }
    }

    return true;
}

bool isZeroIntegerLiteral(const(ubyte)[] literal) {
    if (literal.empty) {
        return false;
    }

    bool hasDigit = false;
    bool allDigitsAreZero = true;
    if (literal.length >= 2 && literal[0] == '0' && literal[1].among('x', 'X')) {
        foreach (c; literal[2 .. $]) {
            if (c == '\'') {
                continue;
            }
            if (!isHexDigit(c)) {
                return false;
            }
            if (c != '0') {
                allDigitsAreZero = false;
            }
            hasDigit = true;
        }
        return hasDigit && allDigitsAreZero;
    }

    if (literal.length >= 2 && literal[0] == '0' && literal[1].among('b', 'B')) {
        foreach (c; literal[2 .. $]) {
            if (c == '\'') {
                continue;
            }
            if (!c.among('0', '1')) {
                return false;
            }
            if (c != '0') {
                allDigitsAreZero = false;
            }
            hasDigit = true;
        }
        return hasDigit && allDigitsAreZero;
    }

    foreach (c; literal) {
        if (c == '\'') {
            continue;
        }
        if (!isDigit(c)) {
            return false;
        }
        if (c != '0') {
            allDigitsAreZero = false;
        }
        hasDigit = true;
    }

    return hasDigit && allDigitsAreZero;
}

bool isDigit(ubyte c) @safe pure nothrow @nogc {
    return c >= '0' && c <= '9';
}

bool isHexDigit(ubyte c) @safe pure nothrow @nogc {
    return isDigit(c) || c >= 'a' && c <= 'f' || c >= 'A' && c <= 'F';
}
