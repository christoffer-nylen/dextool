/**
Copyright: Copyright (c) 2026, Joakim Brännström. All rights reserved.
License: MPL-2
*/
module dextool.plugin.mcdc.visitor;

import std.experimental.logger;
import std.stdio : writeln;

import clang.Cursor : Cursor;
import dextool.type : AbsolutePath;
import libclang_ast.ast : Visitor;

@safe:

final class TUVisitor : Visitor {
    import std.string : strip;
    import libclang_ast.ast;

    alias visit = Visitor.visit;

    private AbsolutePath mainFile;
    private bool[string] seen;

    this(AbsolutePath mainFile) nothrow {
        this.mainFile = mainFile;
    }

    override void visit(scope const TranslationUnit v) {
        v.accept(this);
    }

    override void visit(scope const Attribute v) {
        v.accept(this);
    }

    override void visit(scope const Declaration v) {
        v.accept(this);
    }

    override void visit(scope const Expression v) {
        v.accept(this);
    }

    override void visit(scope const Preprocessor v) {
        v.accept(this);
    }

    override void visit(scope const Reference v) {
        v.accept(this);
    }

    override void visit(scope const Statement v) {
        v.accept(this);
    }

    override void visit(scope const BinaryOperator v) {
        maybePrint(v.cursor, "binary");
        v.accept(this);
    }

    override void visit(scope const UnaryOperator v) {
        maybePrint(v.cursor, "unary");
        v.accept(this);
    }

    private void maybePrint(scope const Cursor cursor, string kind) @trusted {
        import std.format : format;

        if (cursor.location.path != mainFile.toString) {
            return;
        }

        auto tokens = cursor.tokens;
        auto text = tokensToText(tokens).strip;
        if (text.length == 0) {
            return;
        }

        if (!containsLogicalOperator(tokens, kind, text)) {
            return;
        }

        auto loc = cursor.location.spelling;
        auto key = format("%s:%s:%s:%s", loc.file.name, loc.line, loc.column, text);
        if (key in seen) {
            return;
        }

        seen[key] = true;
        writeln(loc.file.name, ":", loc.line, ":", loc.column, ": ", text);
    }

    private string tokensToText(T)(T tokens) @trusted {
        import std.array : appender;

        auto app = appender!string();
        bool first = true;
        foreach (token; tokens) {
            if (!first) {
                app.put(" ");
            }
            app.put(token.spelling);
            first = false;
        }
        return app.data;
    }

    private bool containsLogicalOperator(T)(T tokens, string kind, string text) @trusted {
        if (kind == "binary") {
            foreach (token; tokens) {
                if (token.spelling == "&&" || token.spelling == "||") {
                    return true;
                }
            }
            return false;
        }

        if (kind == "unary") {
            return text.length >= 1 && text[0] == '!';
        }

        return false;
    }
}
