/**
Copyright: Copyright (c) 2020, Joakim Brännström. All rights reserved.
License: MPL-2
Author: Joakim Brännström (joakim.brannstrom@gmx.com)

This Source Code Form is subject to the terms of the Mozilla Public License,
v.2.0. If a copy of the MPL was not distributed with this file, You can obtain
one at http://mozilla.org/MPL/2.0/.
*/
module dextool.plugin.mutate.backend.analyze.pass_clang;

import logger = std.experimental.logger;
import std.algorithm : among, map, sort, filter;
import std.array : empty, array;
import std.exception : collectException;
import std.format : formattedWrite;
import std.meta : AliasSeq;
import std.typecons : Nullable, scoped;

import blob_model : Blob;
import my.container.vector : vector, Vector;
import my.gc.refc : RefCounted;

import clang.Cursor : Cursor;
import clang.Eval : Eval;
import clang.Type : Type;
import clang.c.Index : CXTypeKind, CXCursorKind, CXEvalResultKind, CXTokenKind;

import cpptooling.analyzer.clang.cursor_logger : logNode, mixinNodeLog;

import dextool.clang_extensions : getUnderlyingExprNode;

import dextool.type : Path, AbsolutePath;

import dextool.plugin.mutate.backend.analyze.ast : Interval, Location;
import dextool.plugin.mutate.backend.analyze.extensions;
import dextool.plugin.mutate.backend.analyze.utility;
import dextool.plugin.mutate.backend.interface_ : FilesysIO;
import dextool.plugin.mutate.backend.type : Language, SourceLoc, Offset, SourceLocRange;

import analyze = dextool.plugin.mutate.backend.analyze.ast;

alias accept = dextool.plugin.mutate.backend.analyze.extensions.accept;

/** Translate a clang AST to a mutation AST.
 */
RefCounted!(analyze.Ast) toMutateAst(const Cursor root, FilesysIO fio) @safe {
    import cpptooling.analyzer.clang.ast : ClangAST;

    auto visitor = new BaseVisitor(fio);
    scope (exit)
        visitor.dispose;
    auto ast = ClangAST!BaseVisitor(root);
    ast.accept(visitor);

    return visitor.ast;
}

private:

struct OperatorCursor {
    analyze.Expr astOp;

    // both sides are primitive types, in other words no class overloading.
    bool isOverload;

    // the whole expression
    analyze.Location exprLoc;
    DeriveCursorTypeResult exprTy;

    // the operator itself
    analyze.Operator operator;
    analyze.Location opLoc;

    Cursor lhs;
    Cursor rhs;

    /// Add the result to the AST and astOp to the parent.
    /// astOp is set to have two children, lhs and rhs.
    void put(analyze.Node parent, ref analyze.Ast ast) @safe {
        ast.put(astOp, exprLoc);
        ast.put(operator, opLoc);

        exprTy.put(ast);

        if (exprTy.type !is null)
            ast.put(astOp, exprTy.id);

        if (exprTy.symbol !is null)
            ast.put(astOp, exprTy.symId);

        parent.children ~= astOp;
    }
}

Nullable!OperatorCursor operatorCursor(T)(T node) {
    import dextool.clang_extensions : getExprOperator, OpKind, ValueKind, getUnderlyingExprNode;

    auto op = getExprOperator(node.cursor);
    if (!op.isValid)
        return typeof(return)();

    auto path = op.cursor.location.path.Path;
    if (path.empty)
        return typeof(return)();

    OperatorCursor res;

    void sidesPoint() {
        auto sides = op.sides;
        if (sides.lhs.isValid) {
            res.lhs = getUnderlyingExprNode(sides.lhs);
        }
        if (sides.rhs.isValid) {
            res.rhs = getUnderlyingExprNode(sides.rhs);
        }
    }

    // the operator itself
    void opPoint() {
        auto loc = op.location;
        auto sr = loc.spelling;
        res.operator = new analyze.Operator;
        res.opLoc = new analyze.Location(path, Interval(sr.offset,
                cast(uint)(sr.offset + op.length)), SourceLocRange(SourceLoc(loc.line,
                loc.column), SourceLoc(loc.line, cast(uint)(loc.column + op.length))));
    }

    // the arguments and the operator
    void exprPoint() {
        auto sr = op.cursor.extent;
        res.exprLoc = new analyze.Location(path, Interval(sr.start.offset,
                sr.end.offset), SourceLocRange(SourceLoc(sr.start.line,
                sr.start.column), SourceLoc(sr.end.line, sr.end.column)));
        res.exprTy = deriveCursorType(op.cursor);
        switch (op.kind) with (OpKind) {
        case OO_Star: // "*"
            res.isOverload = true;
            goto case;
        case Mul: // "*"
            res.astOp = new analyze.OpMul;
            break;
        case OO_Slash: // "/"
            res.isOverload = true;
            goto case;
        case Div: // "/"
            res.astOp = new analyze.OpDiv;
            break;
        case OO_Percent: // "%"
            res.isOverload = true;
            goto case;
        case Rem: // "%"
            res.astOp = new analyze.OpMod;
            break;
        case OO_Plus: // "+"
            res.isOverload = true;
            goto case;
        case Add: // "+"
            res.astOp = new analyze.OpAdd;
            break;
        case OO_Minus: // "-"
            res.isOverload = true;
            goto case;
        case Sub: // "-"
            res.astOp = new analyze.OpSub;
            break;
        case OO_Less: // "<"
            res.isOverload = true;
            goto case;
        case LT: // "<"
            res.astOp = new analyze.OpLess;
            break;
        case OO_Greater: // ">"
            res.isOverload = true;
            goto case;
        case GT: // ">"
            res.astOp = new analyze.OpGreater;
            break;
        case OO_LessEqual: // "<="
            res.isOverload = true;
            goto case;
        case LE: // "<="
            res.astOp = new analyze.OpLessEq;
            break;
        case OO_GreaterEqual: // ">="
            res.isOverload = true;
            goto case;
        case GE: // ">="
            res.astOp = new analyze.OpGreaterEq;
            break;
        case OO_EqualEqual: // "=="
            res.isOverload = true;
            goto case;
        case EQ: // "=="
            res.astOp = new analyze.OpEqual;
            break;
        case OO_Exclaim: // "!"
            res.isOverload = true;
            goto case;
        case LNot: // "!"
            res.astOp = new analyze.OpNegate;
            break;
        case OO_ExclaimEqual: // "!="
            res.isOverload = true;
            goto case;
        case NE: // "!="
            res.astOp = new analyze.OpNotEqual;
            break;
        case OO_AmpAmp: // "&&"
            res.isOverload = true;
            goto case;
        case LAnd: // "&&"
            res.astOp = new analyze.OpAnd;
            break;
        case OO_PipePipe: // "||"
            res.isOverload = true;
            goto case;
        case LOr: // "||"
            res.astOp = new analyze.OpOr;
            break;
        case OO_Amp: // "&"
            res.isOverload = true;
            goto case;
        case And: // "&"
            res.astOp = new analyze.OpAndBitwise;
            break;
        case OO_Pipe: // "|"
            res.isOverload = true;
            goto case;
        case Or: // "|"
            res.astOp = new analyze.OpOrBitwise;
            break;
        case OO_StarEqual: // "*="
            res.isOverload = true;
            goto case;
        case MulAssign: // "*="
            res.astOp = new analyze.OpAssignMul;
            break;
        case OO_SlashEqual: // "/="
            res.isOverload = true;
            goto case;
        case DivAssign: // "/="
            res.astOp = new analyze.OpAssignDiv;
            break;
        case OO_PercentEqual: // "%="
            res.isOverload = true;
            goto case;
        case RemAssign: // "%="
            res.astOp = new analyze.OpAssignMod;
            break;
        case OO_PlusEqual: // "+="
            res.isOverload = true;
            goto case;
        case AddAssign: // "+="
            res.astOp = new analyze.OpAssignAdd;
            break;
        case OO_MinusEqual: // "-="
            res.isOverload = true;
            goto case;
        case SubAssign: // "-="
            res.astOp = new analyze.OpAssignSub;
            break;
        case OO_AmpEqual: // "&="
            res.isOverload = true;
            goto case;
        case AndAssign: // "&="
            res.astOp = new analyze.OpAssignAndBitwise;
            break;
        case OO_PipeEqual: // "|="
            res.isOverload = true;
            goto case;
        case OrAssign: // "|="
            res.astOp = new analyze.OpAssignOrBitwise;
            break;
        case OO_CaretEqual: // "^="
            res.isOverload = true;
            goto case;
        case OO_Equal: // "="
            goto case;
        case ShlAssign: // "<<="
            goto case;
        case ShrAssign: // ">>="
            goto case;
        case XorAssign: // "^="
            goto case;
        case Assign: // "="
            res.astOp = new analyze.OpAssign;
            break;
            //case Xor: // "^"
            //case OO_Caret: // "^"
            //case OO_Tilde: // "~"
        default:
            res.astOp = new analyze.BinaryOp;
        }
    }

    exprPoint;
    opPoint;
    sidesPoint;
    return typeof(return)(res);
}

struct CaseStmtCursor {
    analyze.Location branch;
    analyze.Location insideBranch;

    Cursor inner;
}

Nullable!CaseStmtCursor caseStmtCursor(T)(T node) {
    import dextool.clang_extensions : getCaseStmt;

    auto mp = getCaseStmt(node.cursor);
    if (!mp.isValid)
        return typeof(return)();

    auto path = node.cursor.location.path.Path;
    if (path.empty)
        return typeof(return)();

    auto extent = node.cursor.extent;

    CaseStmtCursor res;
    res.inner = mp.subStmt;

    auto sr = res.inner.extent;

    auto insideLoc = SourceLocRange(SourceLoc(sr.start.line, sr.start.column),
            SourceLoc(sr.end.line, sr.end.column));
    auto offs = Interval(sr.start.offset, sr.end.offset);
    if (res.inner.kind == CXCursorKind.caseStmt) {
        auto colon = mp.colonLocation;
        insideLoc.begin = SourceLoc(colon.line, colon.column + 1);
        insideLoc.end = insideLoc.begin;

        // a case statement with fallthrough. the only point to inject a bomb
        // is directly after the semicolon
        offs.begin = colon.offset + 1;
        offs.end = offs.begin;
    } else if (res.inner.kind != CXCursorKind.compoundStmt) {
        offs.end = findTokenOffset(node.cursor.translationUnit.cursor.tokens,
                offs, CXTokenKind.punctuation);
    }

    void subStmt() {
        res.insideBranch = new analyze.Location(path, offs, insideLoc);
    }

    void stmt() {
        auto loc = extent.start;
        auto loc_end = extent.end;
        // reuse the end from offs because it covers either only the
        // fallthrough OR also the end semicolon
        auto stmt_offs = Interval(extent.start.offset, offs.end);
        res.branch = new analyze.Location(path, stmt_offs,
                SourceLocRange(SourceLoc(loc.line, loc.column),
                    SourceLoc(loc_end.line, loc_end.column)));
    }

    stmt;
    subStmt;
    return typeof(return)(res);
}

@safe:

Location toLocation(ref const Cursor c) {
    auto e = c.extent;
    auto interval = Interval(e.start.offset, e.end.offset);
    auto begin = e.start;
    auto end = e.end;
    return new Location(e.path.Path, interval, SourceLocRange(SourceLoc(begin.line,
            begin.column), SourceLoc(end.line, end.column)));
}

/** Find all mutation points that affect a whole expression.
 *
 * TODO change the name of the class. It is more than just an expression
 * visitor.
 *
 * # Usage of kind_stack
 * All usage of the kind_stack shall be documented here.
 *  - track assignments to avoid generating unary insert operators for the LHS.
 */
final class BaseVisitor : ExtendedVisitor {
    import clang.c.Index : CXCursorKind, CXTypeKind;
    import cpptooling.analyzer.clang.ast;
    import dextool.clang_extensions : getExprOperator, OpKind;

    alias visit = ExtendedVisitor.visit;

    // the depth the visitor is at.
    uint indent;
    // A stack of the nodes that are generated up to the current one.
    Stack!(analyze.Node) nstack;

    // A stack of visited cursors up to the current one.
    Stack!(CXCursorKind) cstack;

    /// The elements that where removed from the last decrement.
    Vector!(analyze.Node) lastDecr;

    /// List of macro locations which blacklist mutants that would be injected
    /// in any of them.
    BlackList blacklist;

    RefCounted!(analyze.Ast) ast;

    FilesysIO fio;

    this(FilesysIO fio) nothrow {
        this.fio = fio;
        this.ast = analyze.Ast.init;
    }

    void dispose() {
        ast.release;
    }

    /// Returns: the depth (1+) if any of the parent nodes is `k`.
    uint isParent(CXCursorKind k) {
        return cstack.isParent(k);
    }

    /// Returns: if the previous nodes is a CXCursorKind `k`.
    bool isDirectParent(CXCursorKind k) {
        if (cstack.empty)
            return false;
        return cstack[$ - 1].data == k;
    }

    override void incr() @safe {
        ++indent;
        lastDecr.clear;
    }

    override void decr() @trusted {
        --indent;
        lastDecr = nstack.popUntil(indent);
        cstack.popUntil(indent);
    }

    private void pushStack(analyze.Node n, analyze.Location l, const CXCursorKind cKind) @trusted {
        n.blacklist = n.blacklist || blacklist.inside(l);
        n.schemaBlacklist = n.schemaBlacklist || blacklist.blockSchema(l);
        if (!nstack.empty)
            n.schemaBlacklist = n.schemaBlacklist || nstack[$ - 1].data.schemaBlacklist;
        nstack.put(n, indent);
        cstack.put(cKind, indent);
        ast.put(n, l);
    }

    /// Returns: true if it is OK to modify the cursor
    private void pushStack(AstT, ClangT)(AstT n, ClangT c) @trusted {
        auto loc = c.cursor.toLocation;
        nstack.back.children ~= n;
        pushStack(n, loc, c.kind);
    }

    override void visit(const TranslationUnit v) {
        import clang.c.Index : CXLanguageKind;

        mixin(mixinNodeLog!());

        blacklist = BlackList(v.cursor);

        ast.root = new analyze.TranslationUnit;
        auto loc = v.cursor.toLocation;
        pushStack(ast.root, loc, v.cursor.kind);

        // it is most often invalid
        switch (v.cursor.language) {
        case CXLanguageKind.c:
            ast.lang = Language.c;
            break;
        case CXLanguageKind.cPlusPlus:
            ast.lang = Language.cpp;
            break;
        default:
            ast.lang = Language.assumeCpp;
        }

        v.accept(this);
    }

    override void visit(const Attribute v) {
        mixin(mixinNodeLog!());
        v.accept(this);
    }

    override void visit(const Declaration v) {
        mixin(mixinNodeLog!());
        v.accept(this);
    }

    override void visit(const VarDecl v) @trusted {
        mixin(mixinNodeLog!());
        visitVar(v);
        v.accept(this);
    }

    override void visit(const ParmDecl v) @trusted {
        mixin(mixinNodeLog!());
        visitVar(v);
        v.accept(this);
    }

    override void visit(const ClassTemplate v) {
        mixin(mixinNodeLog!());
        // by adding the node it is possible to search for it in cstack
        pushStack(new analyze.Poision, v);
        v.accept(this);
    }

    override void visit(const ClassTemplatePartialSpecialization v) {
        mixin(mixinNodeLog!());
        // by adding the node it is possible to search for it in cstack
        pushStack(new analyze.Poision, v);
        v.accept(this);
    }

    override void visit(const TemplateTypeParameter v) {
        mixin(mixinNodeLog!());
        // block mutants inside template parameters
    }

    override void visit(const TemplateTemplateParameter v) {
        mixin(mixinNodeLog!());
        // block mutants inside template parameters
    }

    override void visit(const NonTypeTemplateParameter v) {
        mixin(mixinNodeLog!());
        // block mutants inside template parameters
    }

    override void visit(const TypeAliasDecl v) {
        mixin(mixinNodeLog!());
        // block mutants inside template parameters
    }

    override void visit(const CxxBaseSpecifier v) {
        mixin(mixinNodeLog!());
        // block mutants inside template parameters.
        // the only mutants that are inside an inheritance is template
        // parameters and such.
    }

    private void visitVar(T)(T v) @trusted {
        auto n = new analyze.VarDecl;

        auto ty = v.cursor.type;
        if (ty.isValid) {
            n.isConst = ty.isConst;
        }

        pushStack(n, v);
    }

    override void visit(const Directive v) {
        mixin(mixinNodeLog!());
        v.accept(this);
    }

    override void visit(const Reference v) {
        mixin(mixinNodeLog!());
        v.accept(this);
    }

    override void visit(const Statement v) {
        mixin(mixinNodeLog!());
        v.accept(this);
    }

    override void visit(const Expression v) {
        import cpptooling.analyzer.clang.ast : dispatch;
        import dextool.clang_extensions : getUnderlyingExprNode;

        mixin(mixinNodeLog!());

        auto ue = Cursor(getUnderlyingExprNode(v.cursor));
        if (ue.isValid && ue != v.cursor) {
            incr;
            scope (exit)
                decr;
            dispatch(ue, this);
        } else {
            pushStack(new analyze.Expr, v);
            v.accept(this);
        }
    }

    override void visit(const Preprocessor v) {
        mixin(mixinNodeLog!());

        const bool isCpp = v.spelling == "__cplusplus";

        if (isCpp)
            ast.lang = Language.cpp;
        else if (!isCpp && ast.lang != Language.cpp)
            ast.lang = Language.c;

        v.accept(this);
    }

    override void visit(const EnumDecl v) @trusted {
        mixin(mixinNodeLog!());

        import std.typecons : scoped;

        // extract the boundaries of the enum to update the type db.
        auto vis = scoped!EnumVisitor(indent);
        vis.visit(v);
        ast.types.set(vis.id, vis.toType);
    }

    override void visit(const FunctionDecl v) @trusted {
        mixin(mixinNodeLog!());
        visitFunc(v);
    }

    override void visit(const Constructor v) @trusted {
        mixin(mixinNodeLog!());

        // skip all "= default" constructors.
        if (!v.cursor.isDefaulted)
            v.accept(this);
    }

    override void visit(const CxxMethod v) {
        mixin(mixinNodeLog!());

        // model C++ methods as functions. It should be enough to know that it
        // is a function and the return type when generating mutants.
        visitFunc(v);
    }

    override void visit(const BreakStmt v) {
        mixin(mixinNodeLog!());
        v.accept(this);
    }

    override void visit(const BinaryOperator v) @trusted {
        mixin(mixinNodeLog!());
        visitOp(v, v.cursor.kind);
    }

    override void visit(const UnaryOperator v) @trusted {
        mixin(mixinNodeLog!());
        visitOp(v, v.cursor.kind);
    }

    override void visit(const CompoundAssignOperator v) {
        mixin(mixinNodeLog!());
        // TODO: implement all aor assignment such as +=
        pushStack(new analyze.OpAssign, v);
        v.accept(this);
    }

    override void visit(const CallExpr v) @trusted {
        mixin(mixinNodeLog!());

        if (visitOp(v, v.cursor.kind))
            return;

        auto n = new analyze.Call;

        // try associate a type with the call
        auto uc = Cursor(getUnderlyingExprNode(v.cursor));
        if (uc.isValid) {
            auto cty = uc.type.canonicalType;
            auto ty = deriveType(cty);
            ty.put(ast);
            if (ty.type !is null)
                ast.put(n, ty.id);
        }

        pushStack(n, v);
        v.accept(this);
    }

    override void visit(const CxxThrowExpr v) {
        mixin(mixinNodeLog!());
        // model a C++ exception as a return expression because that is
        // "basically" what happens.
        pushStack(new analyze.Return, v);
        v.accept(this);
    }

    override void visit(const InitListExpr v) {
        mixin(mixinNodeLog!());
        pushStack(new analyze.Constructor, v);
        v.accept(this);
    }

    override void visit(const LambdaExpr v) @trusted {
        mixin(mixinNodeLog!());

        // model C++ lambdas as functions. It should be enough to know that it
        // is a function and the return type when generating mutants.
        visitFunc(v);
    }

    override void visit(const ReturnStmt v) {
        mixin(mixinNodeLog!());
        pushStack(new analyze.Return, v);
        v.accept(this);
    }

    override void visit(const CompoundStmt v) {
        import std.algorithm : min;

        mixin(mixinNodeLog!());

        static uint findBraketOffset(Blob file, const uint begin, const uint end, const ubyte letter) {
            for (uint i = begin; i < end; ++i) {
                if (file.content[i] == letter) {
                    return i;
                }
            }
            return begin;
        }

        if (isDirectParent(CXCursorKind.switchStmt)) {
            // the CompoundStmt statement {} directly inside a switch statement
            // isn't useful to manipulate as a block. The useful part is the
            // smaller blocks that the case and default break down the block
            // into thus this avoid generating useless blocks that lead to
            // equivalent or unproductive mutants.
        } else
            try {
                auto loc = v.cursor.toLocation;
                auto file = fio.makeInput(loc.file);
                const maxEnd = file.content.length;

                // The block that can be modified is the inside of it thus the
                // a CompoundStmt that represent a "{..}" can for example be the
                // body of a function or the block that a try statement encompase.
                // done then a SDL can't be generated that delete the inside of
                // e.g. void functions.

                auto end = min(findBraketOffset(file, loc.interval.end == 0
                        ? loc.interval.end : loc.interval.end - 1, cast(uint) maxEnd,
                        cast(ubyte) '}'), maxEnd);
                auto begin = findBraketOffset(file, loc.interval.begin, end, cast(ubyte) '{');

                if (begin < end)
                    begin = begin + 1;

                // TODO: need to adjust sloc too
                loc.interval = Interval(begin, end);

                auto n = new analyze.Block;
                nstack.back.children ~= n;
                pushStack(n, loc, v.cursor.kind);
            } catch (Exception e) {
                logger.trace(e.msg).collectException;
            }

        v.accept(this);
    }

    override void visit(const CaseStmt v) {
        mixin(mixinNodeLog!());

        if (isDirectParent(CXCursorKind.caseStmt)) {
            // the previous case statement was a fallthrough.
            rewriteCaseToFallthrough(ast, nstack[$ - 2].data);
        }

        auto res = caseStmtCursor(v);
        if (res.isNull) {
            pushStack(new analyze.Block, v);
            v.accept(this);
            return;
        }

        auto branch = new analyze.Branch;
        nstack.back.children ~= branch;
        pushStack(branch, res.get.branch, v.cursor.kind);

        // create a node depth that diverge from the clang AST wherein the
        // inside of a case stmt is modelled as a block.
        incr;
        scope (exit)
            decr;

        auto inner = new analyze.Block;
        branch.children ~= inner;
        branch.inside = inner;
        pushStack(inner, res.get.insideBranch, v.cursor.kind);

        dispatch(res.get.inner, this);
    }

    override void visit(const DefaultStmt v) {
        mixin(mixinNodeLog!());

        if (isDirectParent(CXCursorKind.caseStmt)) {
            // the previous case statement was a fallthrough.
            rewriteCaseToFallthrough(ast, nstack[$ - 2].data);
        }

        auto branch = new analyze.Branch;
        pushStack(branch, v);

        incr;
        scope (exit)
            decr;

        auto loc = () {
            auto loc = ast.location(branch);
            auto l = new analyze.Location(loc.file, loc.interval, loc.sloc);

            const default_ = "default:";
            if ((l.interval.end - l.interval.begin) < default_.length) {
                return l;
            }
            l.interval.begin += default_.length;
            l.sloc.begin.column += default_.length;
            return l;
        }();

        auto inside = new analyze.Block;
        branch.inside = inside;
        branch.children ~= inside;
        pushStack(inside, loc, v.cursor.kind);

        branch.children = [inside];

        v.accept(this);
    }

    override void visit(const ForStmt v) {
        mixin(mixinNodeLog!());
        pushStack(new analyze.Loop, v);

        auto visitor = new FindVisitor!CompoundStmt;
        v.accept(visitor);

        if (visitor.node !is null) {
            this.visit(visitor.node);
        }
    }

    override void visit(const CxxForRangeStmt v) {
        mixin(mixinNodeLog!());
        pushStack(new analyze.Loop, v);

        auto visitor = new FindVisitor!CompoundStmt;
        v.accept(visitor);

        if (visitor.node !is null) {
            this.visit(visitor.node);
        }
    }

    override void visit(const WhileStmt v) {
        mixin(mixinNodeLog!());
        pushStack(new analyze.Loop, v);
        v.accept(this);
    }

    override void visit(const DoStmt v) {
        mixin(mixinNodeLog!());
        pushStack(new analyze.Loop, v);
        v.accept(this);
    }

    override void visit(const SwitchStmt v) {
        mixin(mixinNodeLog!());
        auto n = new analyze.BranchBundle;
        pushStack(n, v);
        v.accept(this);
        rewriteSwitch(ast, n);
    }

    override void visit(const IfStmt v) @trusted {
        mixin(mixinNodeLog!());
        pushStack(new analyze.BranchBundle, v);
        dextool.plugin.mutate.backend.analyze.extensions.accept(v, this);
    }

    override void visit(const IfStmtCond v) {
        mixin(mixinNodeLog!());
        pushStack(new analyze.Condition, v);

        incr;
        scope (exit)
            decr;
        if (!visitOp(v, v.cursor.kind)) {
            v.accept(this);
        }
    }

    override void visit(const IfStmtThen v) {
        mixin(mixinNodeLog!());
        pushStack(new analyze.Branch, v);
        v.accept(this);
    }

    override void visit(const IfStmtElse v) {
        mixin(mixinNodeLog!());
        pushStack(new analyze.Branch, v);
        v.accept(this);
    }

    private bool visitOp(T)(ref const T v, const CXCursorKind cKind) @trusted {
        auto op = operatorCursor(v);
        if (op.isNull) {
            return false;
        }

        if (visitBinaryOp(op.get, cKind))
            return true;
        return visitUnaryOp(op.get, cKind);
    }

    /// Returns: true if it added a binary operator, false otherwise.
    private bool visitBinaryOp(ref OperatorCursor op, const CXCursorKind cKind) @trusted {
        import cpptooling.analyzer.clang.ast : dispatch;

        auto astOp = cast(analyze.BinaryOp) op.astOp;
        if (astOp is null)
            return false;

        const blockSchema = op.isOverload || blacklist.blockSchema(op.opLoc)
            || isParent(CXCursorKind.classTemplate)
            || isParent(CXCursorKind.classTemplatePartialSpecialization);

        astOp.schemaBlacklist = blockSchema;
        astOp.operator = op.operator;
        astOp.operator.blacklist = blacklist.inside(op.opLoc);
        astOp.operator.schemaBlacklist = blockSchema;

        op.put(nstack.back, ast);
        pushStack(astOp, op.exprLoc, cKind);
        incr;
        scope (exit)
            decr;

        if (op.lhs.isValid) {
            incr;
            scope (exit)
                decr;
            dispatch(op.lhs, this);
            auto b = () {
                if (!lastDecr.empty)
                    return cast(analyze.Expr) lastDecr[$ - 1];
                return null;
            }();
            if (b !is null && b != astOp) {
                astOp.lhs = b;
                auto ty = deriveCursorType(op.lhs);
                ty.put(ast);
                if (ty.type !is null) {
                    ast.put(b, ty.id);
                }
                if (ty.symbol !is null) {
                    ast.put(b, ty.symId);
                }
            }
        }
        if (op.rhs.isValid) {
            incr;
            scope (exit)
                decr;
            dispatch(op.rhs, this);
            auto b = () {
                if (!lastDecr.empty)
                    return cast(analyze.Expr) lastDecr[$ - 1];
                return null;
            }();
            if (b !is null && b != astOp) {
                astOp.rhs = b;
                auto ty = deriveCursorType(op.rhs);
                ty.put(ast);
                if (ty.type !is null) {
                    ast.put(b, ty.id);
                }
                if (ty.symbol !is null) {
                    ast.put(b, ty.symId);
                }
            }
        }

        return true;
    }

    /// Returns: true if it added a binary operator, false otherwise.
    private bool visitUnaryOp(ref OperatorCursor op, CXCursorKind cKind) @trusted {
        import cpptooling.analyzer.clang.ast : dispatch;

        auto astOp = cast(analyze.UnaryOp) op.astOp;
        if (astOp is null)
            return false;

        astOp.operator = op.operator;
        astOp.operator.blacklist = blacklist.inside(op.opLoc);
        astOp.operator.schemaBlacklist = op.isOverload || blacklist.blockSchema(op.opLoc);

        op.put(nstack.back, ast);
        pushStack(astOp, op.exprLoc, cKind);
        incr;
        scope (exit)
            decr;

        if (op.lhs.isValid) {
            incr;
            scope (exit)
                decr;
            dispatch(op.lhs, this);
            auto b = () {
                if (!lastDecr.empty)
                    return cast(analyze.Expr) lastDecr[$ - 1];
                return null;
            }();
            if (b !is null && b != astOp) {
                astOp.expr = b;
                auto ty = deriveCursorType(op.lhs);
                ty.put(ast);
                if (ty.type !is null) {
                    ast.put(b, ty.id);
                }
                if (ty.symbol !is null) {
                    ast.put(b, ty.symId);
                }
            }
        } else if (op.rhs.isValid) {
            incr;
            scope (exit)
                decr;
            dispatch(op.rhs, this);
            auto b = () {
                if (!lastDecr.empty)
                    return cast(analyze.Expr) lastDecr[$ - 1];
                return null;
            }();
            if (b !is null && b != astOp) {
                astOp.expr = b;
                auto ty = deriveCursorType(op.rhs);
                ty.put(ast);
                if (ty.type !is null) {
                    ast.put(b, ty.id);
                }
                if (ty.symbol !is null) {
                    ast.put(b, ty.symId);
                }
            }
        }

        return true;
    }

    private void visitFunc(T)(ref const T v) @trusted {
        auto loc = v.cursor.toLocation;
        auto n = new analyze.Function;
        n.schemaBlacklist = isConstExpr(v.cursor);
        nstack.back.children ~= n;
        pushStack(n, loc, v.cursor.kind);

        auto fRetval = new analyze.Return;
        auto rty = deriveType(v.cursor.func.resultType);
        rty.put(ast);
        if (rty.type !is null) {
            ast.put(fRetval, loc);
            n.return_ = fRetval;
            ast.put(fRetval, rty.id);
        }
        if (rty.symbol !is null) {
            ast.put(fRetval, rty.symId);
        }

        v.accept(this);
    }
}

final class EnumVisitor : ExtendedVisitor {
    import std.typecons : Nullable;
    import cpptooling.analyzer.clang.ast;

    alias visit = ExtendedVisitor.visit;

    mixin generateIndentIncrDecr;

    analyze.TypeId id;
    Nullable!long minValue;
    Nullable!long maxValue;

    this(const uint indent) {
        this.indent = indent;
    }

    override void visit(const EnumDecl v) @trusted {
        mixin(mixinNodeLog!());
        id = make!(analyze.TypeId)(v.cursor);
        v.accept(this);
    }

    override void visit(const EnumConstantDecl v) @trusted {
        mixin(mixinNodeLog!());

        long value = v.cursor.enum_.signedValue;

        if (minValue.isNull) {
            minValue = value;
            maxValue = value;
        }

        if (value < minValue.get)
            minValue = value;
        if (value > maxValue.get)
            maxValue = value;

        v.accept(this);
    }

    analyze.Type toType() const {
        auto l = () {
            if (minValue.isNull)
                return analyze.Value(analyze.Value.NegInf.init);
            return analyze.Value(analyze.Value.Int(minValue.get));
        }();
        auto u = () {
            if (maxValue.isNull)
                return analyze.Value(analyze.Value.PosInf.init);
            return analyze.Value(analyze.Value.Int(maxValue.get));
        }();

        return new analyze.DiscreteType(analyze.Range(l, u));
    }
}

final class FindVisitor(T) : ExtendedVisitor {
    import clang.c.Index : CXCursorKind, CXTypeKind;
    import cpptooling.analyzer.clang.ast;

    alias visit = ExtendedVisitor.visit;

    T node;

    override void visit(const T v) @trusted {
        node = cast() v;
    }
}

/** Rewrite the node to correctly represent a case statement as a fallthrough.
 *
 * - Branch
 *      - Block
 *
 * to a Branch which only covers the `case X:` and an empty block
 */
void rewriteCaseToFallthrough(ref analyze.Ast ast, analyze.Node node) {
    if (node.kind != analyze.Kind.Branch) {
        return;
    }

    auto branch = cast(analyze.Branch) node;

    auto loc = ast.location(branch);
    auto iloc = ast.location(branch.inside);

    loc.interval.end = iloc.interval.begin;
    loc.sloc.end = iloc.sloc.begin;

    iloc.interval.end = iloc.interval.begin;
    iloc.sloc.end = iloc.sloc.begin;
}

/** Rewrite the structure of a switch statement from:
 * BranchBundle
 *  - Branch
 *      - Block
 *          - Node
 *  - Node
 *
 * to:
 * BranchBundle
 *  - Branch
 *      - Block
 *          - Node
 *          - Node
 *
 * TODO: This function now "works" but probably contains redundant
 * functionality and is inefficient. Simplify the implementation.
 */
void rewriteSwitch(ref analyze.Ast ast, analyze.BranchBundle root) {
    import std.array : appender;
    import my.container.vector;

    //logger.trace("before rewrite:\n", ast.toString);

    // flatten the case branches and their interior one level to handle e.g.
    // case with fallthrough.
    static analyze.Node[] flatten(analyze.Node[] nodes) @trusted {
        auto app = appender!(analyze.Node[])();
        foreach (n; nodes) {
            app.put(n);
            //logger.tracef("%s children %s", n.kind, n.children.map!(a => a.kind));
            if (n.kind == analyze.Kind.Branch) {
                // the expected case, one child with one block.
                // for a nested
                if (n.children.length == 1 && n.children[0].kind == analyze.Kind.Block) {
                    app.put(flatten(n.children[0].children));
                    n.children[0].children = null;
                } else if (n.children.length > 1 && n.children[0].kind == analyze.Kind.Block) {
                    app.put(n.children[0].children);
                    app.put(n.children[1 .. $]);

                    n.children[0].children = null;
                    n.children = n.children[0 .. 1];
                } else {
                    app.put(n.children);
                    n.children = null;
                }
            }
        }
        //import std.format;
        //logger.info(app.data.map!(a => format("%s (%X)", a.kind, cast(void*) a)));
        return app.data;
    }

    // change loc of `n`s end to be that of its largest child, nested.
    void expandLoc(analyze.Node n) {
        if (n.children.empty || n.kind != analyze.Kind.Branch) {
            return;
        }

        // largest node of the parent.
        static analyze.Node largestNode(ref analyze.Ast ast, analyze.Node curr,
                analyze.Node candidate) {
            auto rval = candidate;
            auto rvall = ast.location(candidate);
            foreach (n; curr.children) {
                auto c = largestNode(ast, n, rval);
                auto l = ast.location(c);
                if (l.interval.end > rvall.interval.end) {
                    rval = c;
                    rvall = l;
                }
            }

            return rval;
        }

        auto branch = cast(analyze.Branch) n;
        auto last = () {
            auto loc = ast.location(branch.inside);
            if (loc.interval.begin == loc.interval.end) {
                // a fallthrough case branch
                return branch.inside;
            }
            auto ln = largestNode(ast, n, n);
            auto lnloc = ast.location(ln);
            if (lnloc.interval.end < loc.interval.end) {
                return branch.inside;
            }
            return ln;
        }();

        auto cloc = ast.location(last);

        {
            auto loc = ast.location(n);
            loc.interval.end = cloc.interval.end;
            loc.sloc.end = cloc.sloc.end;
        }

        if (branch.children.length == 1 && branch.children[0].kind == analyze.Kind.Block) {
            auto loc = ast.location(branch.children[0]);
            loc.interval.end = cloc.interval.end;
            loc.sloc.end = cloc.sloc.end;
        }
    }

    // contract all locs of `n` to not go over the boundary `bottom`.
    static void contractLocRecursive(ref analyze.Ast ast, analyze.Node root, Location bottom) {
        void contract(analyze.Node n) {
            auto l = ast.location(n);
            if (l.interval.end > bottom.interval.begin) {
                l.interval.end = bottom.interval.begin;
                l.sloc.end = bottom.sloc.begin;
            }
        }

        contract(root);
        foreach (c; root.children) {
            contractLocRecursive(ast, c, bottom);
        }
    }

    // remove the expression nodes of the switch statement.
    static analyze.Node[] popUntilBranch(analyze.Node[] nodes) {
        foreach (i; 0 .. nodes.length) {
            if (nodes[i].kind == analyze.Kind.Branch) {
                return nodes[i .. $];
            }
        }
        return null;
    }

    auto nodes = popUntilBranch(root.children);
    if (nodes is null) {
        // the switch is in such a state that any mutation of it will
        // result in unknown problems. just drop its content all together
        // and thus blocking mutations of it.
        root.children = null;
        return;
    }
    nodes = flatten(nodes);

    Vector!(analyze.Node) rootChildren;
    analyze.Node curr = nodes[0];
    auto merge = appender!(analyze.Node[])();

    void updateNode(analyze.Node n) {
        //() @trusted {
        //logger.tracef("%s %X", n.kind, cast(const(void)*) n);
        //}();
        if (curr.children.length >= 1 && curr.children[0].kind == analyze.Kind.Block) {
            curr.children[0].children = merge.data.dup;
        } else {
            curr.children = merge.data.dup;
        }
        merge.clear;

        expandLoc(curr);
        rootChildren.put(curr);
        curr = n;
    }

    foreach (n; nodes[1 .. $]) {
        if (n.kind == analyze.Kind.Branch) {
            updateNode(n);
        } else {
            merge.put(n);
        }
    }

    if (!merge.data.empty) {
        updateNode(curr);
    }

    if (rootChildren.length > 1) {
        foreach (i; 0 .. rootChildren.length - 1) {
            contractLocRecursive(ast, rootChildren[i], ast.location(rootChildren[i + 1]));
        }
    }

    root.children = rootChildren[];
}

enum discreteCategory = AliasSeq!(CXTypeKind.charU, CXTypeKind.uChar, CXTypeKind.char16,
            CXTypeKind.char32, CXTypeKind.uShort, CXTypeKind.uInt, CXTypeKind.uLong, CXTypeKind.uLongLong,
            CXTypeKind.uInt128, CXTypeKind.charS, CXTypeKind.sChar, CXTypeKind.wChar, CXTypeKind.short_,
            CXTypeKind.int_, CXTypeKind.long_, CXTypeKind.longLong,
            CXTypeKind.int128, CXTypeKind.enum_,);
enum floatCategory = AliasSeq!(CXTypeKind.float_, CXTypeKind.double_,
            CXTypeKind.longDouble, CXTypeKind.float128, CXTypeKind.half, CXTypeKind.float16,);
enum pointerCategory = AliasSeq!(CXTypeKind.nullPtr, CXTypeKind.pointer,
            CXTypeKind.blockPointer, CXTypeKind.memberPointer, CXTypeKind.record);
enum boolCategory = AliasSeq!(CXTypeKind.bool_);

enum voidCategory = AliasSeq!(CXTypeKind.void_);

struct DeriveTypeResult {
    analyze.TypeId id;
    analyze.Type type;
    analyze.SymbolId symId;
    analyze.Symbol symbol;

    void put(ref analyze.Ast ast) @safe {
        if (type !is null) {
            ast.types.require(id, type);
        }
        if (symbol !is null) {
            ast.symbols.require(symId, symbol);
        }
    }
}

DeriveTypeResult deriveType(Type cty) {
    DeriveTypeResult rval;

    auto ctydecl = cty.declaration;
    if (ctydecl.isValid) {
        rval.id = make!(analyze.TypeId)(ctydecl);
    } else {
        rval.id = make!(analyze.TypeId)(cty.cursor);
    }

    if (cty.isEnum) {
        rval.type = new analyze.DiscreteType(analyze.Range.makeInf);
        if (!cty.isSigned) {
            rval.type.range.low = analyze.Value(analyze.Value.Int(0));
        }
    } else if (cty.kind.among(floatCategory)) {
        rval.type = new analyze.ContinuesType(analyze.Range.makeInf);
    } else if (cty.kind.among(pointerCategory)) {
        rval.type = new analyze.UnorderedType(analyze.Range.makeInf);
    } else if (cty.kind.among(boolCategory)) {
        rval.type = new analyze.BooleanType(analyze.Range.makeBoolean);
    } else if (cty.kind.among(discreteCategory)) {
        rval.type = new analyze.DiscreteType(analyze.Range.makeInf);
        if (!cty.isSigned) {
            rval.type.range.low = analyze.Value(analyze.Value.Int(0));
        }
    } else if (cty.kind.among(voidCategory)) {
        rval.type = new analyze.VoidType();
    } else {
        // unknown such as an elaborated
        rval.type = new analyze.Type();
    }

    return rval;
}

struct DeriveCursorTypeResult {
    Cursor expr;
    DeriveTypeResult typeResult;
    alias typeResult this;
}

/** Analyze a cursor to derive the type of it and if it has a concrete value
 * and what it is in that case.
 *
 * This is intended for expression nodes in the clang AST.
 */
DeriveCursorTypeResult deriveCursorType(const Cursor baseCursor) {
    auto c = Cursor(getUnderlyingExprNode(baseCursor));
    if (!c.isValid)
        return DeriveCursorTypeResult.init;

    auto rval = DeriveCursorTypeResult(c);
    auto cty = c.type.canonicalType;
    rval.typeResult = deriveType(cty);

    // evaluate the cursor to add a value for the symbol
    void eval(const ref Eval e) {
        if (!e.kind.among(CXEvalResultKind.int_))
            return;

        const long value = () {
            if (e.isUnsignedInt) {
                const v = e.asUnsigned;
                if (v < long.max)
                    return cast(long) v;
            }
            return e.asLong;
        }();

        rval.symId = make!(analyze.SymbolId)(c);
        rval.symbol = new analyze.DiscretSymbol(analyze.Value(analyze.Value.Int(value)));
    }

    if (cty.isEnum) {
        // TODO: check if c.eval give the same result. If so it may be easier
        // to remove this special case of an enum because it is covered by the
        // generic branch for discretes.

        auto ctydecl = cty.declaration;
        if (!ctydecl.isValid)
            return rval;

        const cref = c.referenced;
        if (!cref.isValid)
            return rval;

        if (cref.kind == CXCursorKind.enumConstantDecl) {
            const long value = cref.enum_.signedValue;
            rval.symId = make!(analyze.SymbolId)(c);
            rval.symbol = new analyze.DiscretSymbol(analyze.Value(analyze.Value.Int(value)));
        }
    } else if (cty.kind.among(discreteCategory)) {
        // crashes in clang 7.x. Investigate why.
        //const e = c.eval;
        //if (e.isValid)
        //    eval(e);
    }

    return rval;
}

auto make(T)(const Cursor c) if (is(T == analyze.TypeId) || is(T == analyze.SymbolId)) {
    const usr = c.usr;
    if (usr.empty) {
        return T(c.toHash);
    }
    return analyze.makeId!T(usr);
}

/// trusted: trusting the impl in clang.
uint findTokenOffset(T)(T toks, Offset sr, CXTokenKind kind) @trusted {
    foreach (ref t; toks) {
        if (t.location.offset >= sr.end) {
            if (t.kind == kind) {
                return t.extent.end.offset;
            }
            break;
        }
    }

    return sr.end;
}

/** Check if a function has the constexpr keyword.
 *
 * The implementation opt for higher precision than efficiency which is why it
 * looks at the tokens. That should eliminate such factors as "whitespace".
 */
bool isConstExpr(const Cursor c) @trusted {
    bool helper(T)(ref T toks) {
        foreach (ref t; toks.filter!(a => a.kind.among(CXTokenKind.keyword,
                CXTokenKind.identifier))) {
            if (t.spelling == "constexpr") {
                return true;
            }
        }
        return false;
    }

    auto toks = c.tokens;
    if (toks.empty) {
        // unknown assuming true. this happens when a constexpr is prefixed by
        // a macro.
        return true;
    }
    return helper(toks);
}

/** Create an index of all macros that then can be queried to see if a Cursor
 * or Interval overlap a macro.
 */
struct BlackList {
    import dextool.plugin.mutate.backend.analyze.utility : Index;

    Index!string macros;
    /// schemas are blacklisted for these
    Index!string schemas;

    this(const Cursor root) {
        Interval[][string] macros;
        Interval[][string] schemas;

        foreach (c, parent; root.all) {
            if (!c.kind.among(CXCursorKind.macroExpansion,
                    CXCursorKind.macroDefinition) || c.isMacroBuiltin)
                continue;

            auto spelling = c.spelling;
            // C code almost always implement these as macros. They should not
            // be blocked from being mutated.
            if (spelling.among("bool", "TRUE", "FALSE")) {
                add(c, schemas);
            } else {
                add(c, macros);
            }
        }

        foreach (k; macros.byKey) {
            macros[k] = macros[k].sort.array;
        }
        foreach (k; schemas.byKey) {
            schemas[k] = schemas[k].sort.array;
        }

        this.macros = Index!string(macros);
        this.schemas = Index!string(schemas);
    }

    void add(const Cursor c, ref Interval[][string] idx) {
        const file = c.location.path;
        const e = c.extent;
        const interval = Interval(e.start.offset, e.end.offset);
        if (auto v = file in idx) {
            (*v) ~= interval;
        } else {
            idx[file] = [interval];
        }
    }

    bool blockSchema(analyze.Location l) {
        return schemas.inside(l.file, l.interval);
    }

    bool inside(const Cursor c) {
        const file = c.location.path.Path;
        const e = c.extent;
        const interval = Interval(e.start.offset, e.end.offset);
        return inside(file, interval);
    }

    bool inside(analyze.Location l) {
        return inside(l.file, l.interval);
    }

    /**
     * assuming that an invalid mutant is always inside a macro thus only
     * checking if the `i` is inside. Removing a "block" of code that happens
     * to contain a macro is totally "ok". It doesn't create any problem.
     *
     * Returns: true if `i` is inside a macro interval.
     */
    bool inside(const Path file, const Interval i) {
        return macros.inside(file, i);
    }
}
