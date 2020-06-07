/**
Copyright: Copyright (c) 2020, Joakim Brännström. All rights reserved.
License: MPL-2
Author: Joakim Brännström (joakim.brannstrom@gmx.com)

This Source Code Form is subject to the terms of the Mozilla Public License,
v.2.0. If a copy of the MPL was not distributed with this file, You can obtain
one at http://mozilla.org/MPL/2.0/.

A language independent AST specific for generating mutants both via the plain
source code manipulation but also mutant schematas.
*/
module dextool.plugin.mutate.backend.analyze.ast;

import logger = std.experimental.logger;
import std.algorithm : map, filter, among;
import std.array : appender;
import std.format : formattedWrite, format;
import std.meta : AliasSeq;
import std.range : isOutputRange;

import sumtype;

import dextool.type : AbsolutePath, Path;

static import dextool.plugin.mutate.backend.type;

@safe:

struct Ast {
    /// The language the mutation AST is based on.
    dextool.plugin.mutate.backend.type.Language lang;

    Location[Node] locs;

    // a node can have a type
    TypeId[Node] nodeTypes;
    Types types;

    // a node can have been resolved to a symbolic value.
    SymbolId[Node] nodeSymbols;
    Symbols symbols;

    Node root;

    void accept(VisitorT)(VisitorT v) {
        v.visit(root);
    }

    void put(Node n, Location l) {
        // TODO: deduplicate the path because it will otherwise take up so much
        // memory.....
        locs[n] = l;
    }

    void put(Node n, TypeId id) {
        nodeTypes[n] = id;
    }

    void put(Node n, SymbolId id) {
        nodeSymbols[n] = id;
    }

    Location location(Node n) {
        if (auto v = n in locs) {
            return *v;
        }
        return null;
    }

    Type type(Node n) {
        if (auto v = n in nodeTypes) {
            return types.get(*v);
        }
        return null;
    }

    Symbol symbol(Node n) {
        if (auto v = n in nodeSymbols) {
            return symbols.get(*v);
        }
        return null;
    }

    string toString() @safe {
        auto buf = appender!string;
        toString(buf);
        return buf.data;
    }

    void toString(Writer)(ref Writer w) if (isOutputRange!(Writer, char)) {
        import std.range : put;

        formattedWrite(w, "Source language: %s\n", lang);

        auto res = () @trusted {
            auto dump = new AstPrintVisitor(&this);
            this.accept(dump);
            return dump.buf.data;
        }();
        put(w, res);

        put(w, "Types:");
        put(w, "\n");
        types.toString(w);
        put(w, "Symbols:");
        put(w, "\n");
        symbols.toString(w);
    }
}

class AstPrintVisitor : DepthFirstVisitor {
    import std.array : Appender;
    import std.range : put, repeat;

    Appender!string buf;
    int depth;
    int prevDepth;
    char[] indent;
    Ast* ast;

    this(Ast* ast) {
        this.ast = ast;
    }

    void toBuf(Node n) {
        import std.conv : to;
        import colorlog : color, Color;

        if (depth == 0) {
            indent = null;
        } else if (depth == prevDepth) {
        } else if (depth > prevDepth) {
            const diff = (depth - prevDepth - 1) * 2;
            if (indent.length == 0) {
            } else if (indent[$ - 2] == '`') {
                indent[$ - 1] = ' ';
                indent[$ - 2] = ' ';
            } else {
                indent[$ - 1] = ' ';
            }

            foreach (_; 0 .. diff)
                indent ~= "  ";

            if (n.children.length <= 1)
                indent ~= "`-";
            else
                indent ~= "|-";
        } else {
            const diff = (prevDepth - depth) * 2;
            indent = indent[0 .. $ - diff];

            if (indent.length != 0 && indent[$ - 2 .. $] == "| ") {
                indent[$ - 1] = '-';
            }
        }
        put(buf, indent);

        void printNode() {
            auto bl = () {
                if (n.blacklist)
                    return " blacklist".color(Color.magenta).toString;
                return "";
            }();
            formattedWrite(buf, "%s %x%s", n.kind.to!string.color(Color.lightGreen), () @trusted {
                return cast(void*) n;
            }().to!string.color(Color.lightYellow), bl);
        }

        void printTypeSymbol(Node n) {
            if (auto tyId = n in ast.nodeTypes) {
                auto ty = ast.types.get(*tyId);
                formattedWrite(buf, " %X", tyId.value);
            }
            if (auto syId = n in ast.nodeSymbols) {
                auto sy = ast.symbols.get(*syId);
                formattedWrite(buf, " %X:%s", syId.value, sy.value);
            }
        }

        switch (n.kind) {
        case Kind.Function:
            printNode;
            printTypeSymbol((cast(Function) n).return_);
            break;
        case Kind.VarDecl:
            printNode;
            if ((cast(VarDecl) n).isConst) {
                put(buf, " const");
            }
            break;
        default:
            printNode;
            if (isExpression(n.kind)) {
                printTypeSymbol(n);
            }
        }

        if (auto l = ast.location(n)) {
            formattedWrite(buf, " <%s:%s>", l.file.color(Color.cyan), l.posToString);
        }
        put(buf, "\n");

        prevDepth = depth;
    }

    static foreach (N; Nodes) {
        override void visit(N n) {
            toBuf(n);
            ++depth;

            auto op = () @trusted {
                if (auto v = cast(BinaryOp) n) {
                    return v.operator;
                } else if (auto v = cast(UnaryOp) n) {
                    return v.operator;
                }
                return null;
            }();
            if (op !is null) {
                visit(op);
            }

            n.accept(this);
            --depth;
        }
    }
}

/// The interval in bytes that the node occupy. It is a closed->open set.
alias Interval = dextool.plugin.mutate.backend.type.Offset;
alias SourceLoc = dextool.plugin.mutate.backend.type.SourceLoc;
alias SourceLocRange = dextool.plugin.mutate.backend.type.SourceLocRange;

class Location {
    AbsolutePath file;
    Interval interval;
    SourceLocRange sloc;

    this(Path f, Interval i, SourceLocRange s) {
        file = f;
        interval = i;
        sloc = s;
    }

    // Convert only the position in the file to a string.
    string posToString() @safe const {
        return format!"[%s:%s-%s:%s]:[%s:%s]"(sloc.begin.line, sloc.begin.column,
                sloc.end.line, sloc.end.column, interval.begin, interval.end);
    }

    override string toString() @safe const {
        return format!"%s:%s"(file, posToString);
    }
}

abstract class Node {
    Kind kind() const;

    Node[] children;

    /** If the node is blacklisted from being mutated. This is for example when
     * the node covers a C macro.
     */
    bool blacklist;
}

/**
 * It is optional to add the members visitPush/visitPop to push/pop the nodes that are visited.
 * The parent will always have been the last pushed.
 */
void accept(VisitorT)(Node n, VisitorT v) {
    static string mixinSwitch() {
        import std.format : format;
        import std.traits : EnumMembers;

        string s;
        s ~= "final switch(c.kind) {\n";
        foreach (k; [EnumMembers!Kind]) {
            s ~= format!"case Kind.%1$s: v.visit(cast(%1$s) c); break;\n"(k);
        }
        s ~= "}";
        return s;
    }

    static if (__traits(hasMember, VisitorT, "visitPush"))
        v.visitPush(n);
    foreach (c; n.children) {
        mixin(mixinSwitch);
    }

    static if (__traits(hasMember, VisitorT, "visitPop"))
        v.visitPop();
}

/// All nodes that a visitor must be able to handle.
// must be sorted such that the leaf nodes are at the top.
// dfmt off
alias Nodes = AliasSeq!(
    BinaryOp,
    Block,
    Branch,
    Call,
    Condition,
    Expr,
    Function,
    Node,
    OpAdd,
    OpAnd,
    OpAndBitwise,
    OpAssign,
    OpAssignAdd,
    OpAssignAndBitwise,
    OpAssignDiv,
    OpAssignMod,
    OpAssignMul,
    OpAssignOrBitwise,
    OpAssignSub,
    OpDiv,
    OpEqual,
    OpGreater,
    OpGreaterEq,
    OpLess,
    OpLessEq,
    OpMod,
    OpMul,
    OpNegate,
    OpNotEqual,
    OpOr,
    OpOrBitwise,
    OpSub,
    Operator,
    Return,
    Statement,
    TranslationUnit,
    UnaryOp,
    VarDecl,
    VarRef,
);

// It should be possible to generate the enum from Nodes. How?
enum Kind {
    BinaryOp,
    Block,
    Branch,
    Call,
    Condition,
    Expr,
    Function,
    Node,
    OpAdd,
    OpAnd,
    OpAndBitwise,
    OpAssign,
    OpAssignAdd,
    OpAssignAndBitwise,
    OpAssignDiv,
    OpAssignMod,
    OpAssignMul,
    OpAssignOrBitwise,
    OpAssignSub,
    OpDiv,
    OpEqual,
    OpGreater,
    OpGreaterEq,
    OpLess,
    OpLessEq,
    OpMod,
    OpMul,
    OpNegate,
    OpNotEqual,
    OpOr,
    OpOrBitwise,
    OpSub,
    Operator,
    Return,
    Statement,
    TranslationUnit,
    UnaryOp,
    VarDecl,
    VarRef,
}

bool isExpression(Kind k) @safe pure nothrow @nogc {
    with (Kind) {
        return k.among(
            BinaryOp,
            Call,
            Condition,
            Expr,
            OpAdd,
            OpAnd,
            OpAndBitwise,
            OpAssign,
            OpDiv,
            OpEqual,
            OpGreater,
            OpGreaterEq,
            OpLess,
            OpLessEq,
            OpMod,
            OpMul,
            OpNegate,
            OpNotEqual,
            OpOr,
            OpOrBitwise,
            OpSub,
            Return,
            UnaryOp,
            VarDecl,
            VarRef,
            ) != 0;
    }
}
// dfmt on

interface Visitor {
    static foreach (N; Nodes) {
        void visit(N);
    }
}

// TODO: implement a breath first.
class DepthFirstVisitor : Visitor {
    static foreach (N; Nodes) {
        override void visit(N n) {
            n.accept(this);
        }
    }
}

class TranslationUnit : Node {
    mixin NodeKind;
}

class Statement : Node {
    mixin NodeKind;
}

class Expr : Node {
    mixin NodeKind;
}

/// A function definition.
final class Function : Node {
    mixin NodeKind;

    /// If the function has a return type it is associated with this expression.
    Return return_;
}

/// A function call.
final class Call : Expr {
    mixin NodeKind;
}

/// The operator itself in a binary operator expression.
class Operator : Node {
    mixin NodeKind;
}

/** A block of code such such as a local scope enclosed by brackets, `{}`.
 *
 * It is intended to be possible to delete it. But it may need to be further
 * analyzed for e.g. `Return` nodes.
 */
final class Block : Node {
    mixin NodeKind;
}

/** The node contains all symbols that are used in e.g. operator overload
 * resolution.
 */
final class Scope : Node {
    //Node[] 
}

/** The code for one of the branches resulting from a condition.
 *
 * It can be the branches in a if-else statement or a case branch for languages
 * such as C/C++.
 *
 * The important aspect is that the branch is not an expression. It can't be
 * evaluated to a value of a type.
 */
final class Branch : Node {
    mixin NodeKind;

    // The inside of a branch node wherein code can be injected.
    Block inside;
}

/// Results in the bottom type or up.
final class Return : Expr {
    mixin NodeKind;
}

/// A condition wraps "something" which always evaluates to a boolean.
final class Condition : Expr {
    mixin NodeKind;
}

final class VarDecl : Expr {
    mixin NodeKind;
    bool isConst;
}

final class VarRef : Expr {
    mixin NodeKind;
    // should always refer to something
    VarDecl to;

    this(VarDecl to) {
        this.to = to;
    }

    invariant {
        assert(to !is null);
    }
}

class UnaryOp : Expr {
    mixin NodeKind;

    Operator operator;
    Expr expr;

    this() {
    }

    this(Operator op, Expr expr) {
        this.operator = op;
        this.expr = expr;
    }
}

final class OpNegate : UnaryOp {
    mixin NodeKind;
}

class BinaryOp : Expr {
    mixin NodeKind;

    Operator operator;
    Expr lhs;
    Expr rhs;

    this() {
    }

    this(Operator op, Expr lhs, Expr rhs) {
        this.operator = op;
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

final class OpAssign : BinaryOp {
    mixin NodeKind;
}

final class OpAssignAdd : BinaryOp {
    mixin NodeKind;
}

final class OpAssignSub : BinaryOp {
    mixin NodeKind;
}

final class OpAssignMul : BinaryOp {
    mixin NodeKind;
}

final class OpAssignDiv : BinaryOp {
    mixin NodeKind;
}

final class OpAssignMod : BinaryOp {
    mixin NodeKind;
}

final class OpAssignAndBitwise : BinaryOp {
    mixin NodeKind;
}

final class OpAssignOrBitwise : BinaryOp {
    mixin NodeKind;
}

final class OpAdd : BinaryOp {
    mixin NodeKind;
}

final class OpSub : BinaryOp {
    mixin NodeKind;
}

final class OpMul : BinaryOp {
    mixin NodeKind;
}

final class OpDiv : BinaryOp {
    mixin NodeKind;
}

final class OpMod : BinaryOp {
    mixin NodeKind;
}

final class OpAnd : BinaryOp {
    mixin NodeKind;
}

final class OpAndBitwise : BinaryOp {
    mixin NodeKind;
}

final class OpOr : BinaryOp {
    mixin NodeKind;
}

final class OpOrBitwise : BinaryOp {
    mixin NodeKind;
}

final class OpEqual : BinaryOp {
    mixin NodeKind;
}

final class OpLess : BinaryOp {
    mixin NodeKind;
}

final class OpGreater : BinaryOp {
    mixin NodeKind;
}

final class OpLessEq : BinaryOp {
    mixin NodeKind;
}

final class OpGreaterEq : BinaryOp {
    mixin NodeKind;
}

final class OpNotEqual : BinaryOp {
    mixin NodeKind;
}

RetT makeId(RetT, T)(T data) {
    import dextool.hash : makeCrc64Iso;

    auto a = makeCrc64Iso(cast(const(ubyte)[]) data);
    return RetT(a.c0);
}

RetT makeUniqueId(RetT)() {
    import std.random : uniform;

    return RetT(uniform(long.min, long.max));
}

class Type {
    Range range;

    this() {
        this(Range.makeInf);
    }

    this(Range r) {
        this.range = r;
    }

    TypeKind kind() const {
        return TypeKind.bottom;
    }
}

final class DiscreteType : Type {
    this(Range r) {
        super(r);
    }

    override TypeKind kind() const {
        return TypeKind.discrete;
    }
}

final class ContinuesType : Type {
    this(Range r) {
        super(r);
    }

    override TypeKind kind() const {
        return TypeKind.continues;
    }
}

final class UnorderedType : Type {
    this(Range r) {
        super(r);
    }

    override TypeKind kind() const {
        return TypeKind.unordered;
    }
}

final class BooleanType : Type {
    this(Range r) {
        super(r);
    }

    override TypeKind kind() const {
        return TypeKind.boolean;
    }
}

enum TypeKind {
    // It can be anything, practically useless for mutation testing because it
    // doesn't provide any logic that can be used to e.g. generate
    // "intelligent" ROR mutants.
    bottom,
    /// integers, enums
    discrete,
    /// floating point values
    continues,
    /// no order exists between values in the type thus unable to do ROR
    unordered,
    ///
    boolean,
}

struct Value {
    import std.traits : TemplateArgsOf;

    static struct NegInf {
    }

    static struct PosInf {
    }

    static struct Int {
        // TODO: change to BigInt?
        long value;
    }

    static struct Bool {
        bool value;
    }

    alias Value = SumType!(NegInf, PosInf, Int, Bool);
    Value value;

    static foreach (T; TemplateArgsOf!Value) {
        this(T a) {
            value = Value(a);
        }
    }

    string toString() @safe pure const {
        auto buf = appender!string;
        toString(buf);
        return buf.data;
    }

    void toString(Writer)(ref Writer w) const if (isOutputRange!(Writer, char)) {
        import std.conv : to;
        import std.range : put;

        value.match!((const NegInf a) => put(w, "-inf"), (const PosInf a) => put(w,
                "+inf"), (const Int a) => put(w, a.value.to!string),
                (const Bool a) => put(w, a.value.to!string));
    }
}

struct Range {
    static makeInf() {
        return Range(Value(Value.NegInf.init), Value(Value.PosInf.init));
    }

    static makeBoolean() {
        return Range(Value(Value.Bool(false)), Value(Value.Bool(true)));
    }

    Value low;
    Value up;

    this(Value low, Value up) {
        this.low = low;
        this.up = up;
    }

    enum CompareResult {
        onLowerBound,
        onUpperBound,
        // the value and the range fully overlap each other. This happens when
        // the range is only one value.
        overlap,
        inside,
        outside
    }

    CompareResult compare(Value v) {
        CompareResult negInf() {
            return low.value.match!((Value.NegInf a) => CompareResult.onLowerBound,
                    (Value.PosInf a) => CompareResult.outside,
                    (Value.Int a) => CompareResult.outside, (Value.Bool a) => CompareResult.outside);
        }

        CompareResult posInf() {
            return up.value.match!((Value.NegInf a) => CompareResult.onUpperBound,
                    (Value.PosInf a) => CompareResult.outside,
                    (Value.Int a) => CompareResult.outside, (Value.Bool a) => CompareResult.outside);
        }

        CompareResult value(long v) {
            const l = low.value.match!((Value.NegInf a) => CompareResult.inside,
                    (Value.PosInf a) => CompareResult.outside, (Value.Int a) {
                if (a.value < v)
                    return CompareResult.inside;
                if (a.value == v)
                    return CompareResult.onLowerBound;
                return CompareResult.outside;
            }, (Value.Bool a) => CompareResult.outside);

            const u = up.value.match!((Value.NegInf a) => CompareResult.outside,
                    (Value.PosInf a) => CompareResult.inside, (Value.Int a) {
                if (a.value > v)
                    return CompareResult.inside;
                if (a.value == v)
                    return CompareResult.onUpperBound;
                return CompareResult.outside;
            }, (Value.Bool a) => CompareResult.outside);

            if (l == CompareResult.inside && u == CompareResult.inside)
                return CompareResult.inside;
            if (l == CompareResult.onLowerBound && u == CompareResult.onUpperBound)
                return CompareResult.overlap;
            if (l == CompareResult.onLowerBound)
                return l;
            if (u == CompareResult.onUpperBound)
                return u;
            assert(l == CompareResult.outside || u == CompareResult.outside);
            return CompareResult.outside;
        }

        CompareResult boolean(bool v) {
            // TODO: fix this
            return CompareResult.outside;
        }

        return v.value.match!((Value.NegInf a) => negInf,
                (Value.PosInf a) => posInf, (Value.Int a) => value(a.value),
                (Value.Bool a) => boolean(a.value));
    }

    string toString() @safe pure const {
        auto buf = appender!string;
        toString(buf);
        return buf.data;
    }

    void toString(Writer)(ref Writer w) const if (isOutputRange!(Writer, char)) {
        import std.range : put;

        put(w, "[");
        low.toString(w);
        put(w, ":");
        up.toString(w);
        put(w, "]");
    }
}

struct TypeId {
    ulong value;

    size_t toHash() @safe pure nothrow const @nogc {
        return value.hashOf;
    }
}

TypeId makeTypeId(T)(T data) {
    return makeId!TypeId(data);
}

TypeId makeUniqueTypeId() {
    return makeUniqueId!TypeId;
}

struct Types {
    Type[TypeId] types;

    void require(TypeId id, Type t) {
        if (id !in types) {
            types[id] = t;
        }
    }

    void set(TypeId id, Type t) {
        types[id] = t;
    }

    Type get(TypeId id) {
        if (auto v = id in types) {
            return *v;
        }
        return null;
    }

    bool hasId(TypeId id) {
        return (id in types) !is null;
    }

    string toString() @safe const {
        auto buf = appender!string;
        toString(buf);
        return buf.data;
    }

    void toString(Writer)(ref Writer w) const if (isOutputRange!(Writer, char)) {
        import std.format : formattedWrite;
        import std.range : put;

        foreach (kv; types.byKeyValue) {
            formattedWrite(w, "%X:%s:%s", kv.key.value, kv.value.kind, kv.value.range);
            put(w, "\n");
        }
    }
}

class Symbol {
    Value value;

    this() {
        this(Value(Value.PosInf.init));
    }

    this(Value v) {
        this.value = v;
    }

    SymbolKind kind() const {
        return SymbolKind.unknown;
    }
}

final class DiscretSymbol : Symbol {
    this(Value r) {
        super(r);
    }

    override SymbolKind kind() const {
        return SymbolKind.discret;
    }
}

final class ContinuesSymbol : Symbol {
    this(Value r) {
        super(r);
    }

    override SymbolKind kind() const {
        return SymbolKind.continues;
    }
}

final class BooleanSymbol : Symbol {
    this(Value r) {
        super(r);
    }

    override SymbolKind kind() const {
        return SymbolKind.boolean;
    }
}

enum SymbolKind {
    /// the symbol wasn't able to evaluate to something useful
    unknown,
    /// integers, enums
    discret,
    /// floating point values
    continues,
    ///
    boolean,
}

struct SymbolId {
    ulong value;

    size_t toHash() @safe pure nothrow const @nogc {
        return value.hashOf;
    }
}

SymbolId makeSymbolId(T)(T data) {
    return makeId!SymbolId(data);
}

SymbolId makeUniqueSymbolId() {
    return makeUniqueId!SymbolId;
}

struct Symbols {
    Symbol[SymbolId] symbols;

    void require(SymbolId id, Symbol s) {
        if (id !in symbols) {
            symbols[id] = s;
        }
    }

    void set(SymbolId id, Symbol s) {
        symbols[id] = s;
    }

    Symbol get(SymbolId id) {
        if (auto v = id in symbols) {
            return *v;
        }
        return null;
    }

    bool hasId(SymbolId id) {
        return (id in symbols) !is null;
    }

    string toString() @safe const {
        auto buf = appender!string;
        toString(buf);
        return buf.data;
    }

    void toString(Writer)(ref Writer w) const if (isOutputRange!(Writer, char)) {
        foreach (kv; symbols.byKeyValue) {
            formattedWrite(w, "%X:%s:%s\n", kv.key.value, kv.value.kind, kv.value.value);
        }
    }
}

/// Derive all overload sets
OverloadSet[] derive(ref Ast ast) {
    return typeof(return).init;
}

/// A set of symbols that together is the overload set for the function call
/// resolution.
struct OverloadSet {
    BinaryOp[] set;
}

private:

mixin template NodeKind() {
    override Kind kind() const {
        import std.traits : Unqual;

        mixin("return Kind." ~ Unqual!(typeof(this)).stringof ~ ";");
    }
}

struct StringEntry {
    uint hash;
    uint vptr;
}

// StringValue is a variable-length structure. It has neither proper c'tors nor a
// factory method because the only thing which should be creating these is StringTable.
struct StringValue(T) {
    T value; //T is/should typically be a pointer or a slice
    private size_t length;

    char* lstring() @nogc nothrow pure return  {
        return cast(char*)(&this + 1);
    }

    size_t len() const @nogc nothrow pure @safe {
        return length;
    }

    const(char)* toDchars() const @nogc nothrow pure return  {
        return cast(const(char)*)(&this + 1);
    }

    /// Returns: The content of this entry as a D slice
    inout(char)[] toString() inout @nogc nothrow pure {
        return (cast(inout(char)*)(&this + 1))[0 .. length];
    }
}

struct StringTable(T) {
private:
    StringEntry[] table;
    ubyte*[] pools;
    size_t nfill;
    size_t count;
    size_t countTrigger; // amount which will trigger growing the table

public:
    this(size_t size) nothrow pure {
        import std.math : nextPow2, max;

        table = new StringEntry[max(nextPow2(size), 32)];
    }

    /**
    Looks up the given string in the string table and returns its associated
    value.

    Params:
     s = the string to look up
     length = the length of $(D_PARAM s)
     str = the string to look up

    Returns: the string's associated value, or `null` if the string doesn't
     exist in the string table
    */
    inout(StringValue!T)* lookup(const(char)[] str) inout @nogc nothrow pure {
        const hash = typeid(str).getHash(str);
        const i = findSlot(hash, str);
        return getValue(table[i].vptr);
    }

    /**
    Inserts the given string and the given associated value into the string
    table.

    Params:
     s = the string to insert
     length = the length of $(D_PARAM s)
     ptrvalue = the value to associate with the inserted string
     str = the string to insert
     value = the value to associate with the inserted string

    Returns: the newly inserted value, or `null` if the string table already
     contains the string
    */
    StringValue!(T)* insert(const(char)[] str, T value) nothrow pure {
        const hash = typeid(str).getHash(str);
        size_t i = findSlot(hash, str);
        if (table[i].vptr)
            return null; // already in table
        if (++count > countTrigger) {
            grow();
            i = findSlot(hash, str);
        }
        table[i].hash = hash;
        table[i].vptr = allocValue(str, value);
        // printf("insert %.*s %p\n", cast(int)str.length, str.ptr, table[i].value ?: NULL);
        return getValue(table[i].vptr);
    }

    /// ditto
    StringValue!(T)* insert(const(char)* s, size_t length, T value) nothrow pure {
        return insert(s[0 .. length], value);
    }

    StringValue!(T)* update(const(char)[] str) nothrow pure {
        const(size_t) hash = calcHash(str);
        size_t i = findSlot(hash, str);
        if (!table[i].vptr) {
            if (++count > countTrigger) {
                grow();
                i = findSlot(hash, str);
            }
            table[i].hash = hash;
            table[i].vptr = allocValue(str, T.init);
        }
        // printf("update %.*s %p\n", cast(int)str.length, str.ptr, table[i].value ?: NULL);
        return getValue(table[i].vptr);
    }

    StringValue!(T)* update(const(char)* s, size_t length) nothrow pure {
        return update(s[0 .. length]);
    }

    /********************************
     * Walk the contents of the string table,
     * calling fp for each entry.
     * Params:
     *      fp = function to call. Returns !=0 to stop
     * Returns:
     *      last return value of fp call
     */
    int apply(int function(const(StringValue!T)*) nothrow fp) nothrow {
        foreach (const se; table) {
            if (!se.vptr)
                continue;
            const sv = getValue(se.vptr);
            int result = (*fp)(sv);
            if (result)
                return result;
        }
        return 0;
    }

    /// ditto
    extern (D) int opApply(scope int delegate(const(StringValue!T)*) nothrow dg) nothrow {
        foreach (const se; table) {
            if (!se.vptr)
                continue;
            const sv = getValue(se.vptr);
            int result = dg(sv);
            if (result)
                return result;
        }
        return 0;
    }

private:
    /// Free all memory in use by this StringTable
    void freeMem() nothrow pure {
        foreach (pool; pools)
            mem.xfree(pool);
        mem.xfree(table.ptr);
        mem.xfree(pools.ptr);
        table = null;
        pools = null;
    }

    uint allocValue(const(char)[] str, T value) nothrow pure {
        const(size_t) nbytes = (StringValue!T).sizeof + str.length + 1;
        if (!pools.length || nfill + nbytes > POOL_SIZE) {
            pools = (cast(ubyte**) mem.xrealloc(pools.ptr, (pools.length + 1) * (pools[0]).sizeof))[0
                .. pools.length + 1];
            pools[$ - 1] = cast(ubyte*) mem.xmalloc(nbytes > POOL_SIZE ? nbytes : POOL_SIZE);
            if (mem.isGCEnabled)
                memset(pools[$ - 1], 0xff, POOL_SIZE); // 0xff less likely to produce GC pointer
            nfill = 0;
        }
        StringValue!(T)* sv = cast(StringValue!(T)*)&pools[$ - 1][nfill];
        sv.value = value;
        sv.length = str.length;
        .memcpy(sv.lstring(), str.ptr, str.length);
        sv.lstring()[str.length] = 0;
        const(uint) vptr = cast(uint)(pools.length << POOL_BITS | nfill);
        nfill += nbytes + (-nbytes & 7); // align to 8 bytes
        return vptr;
    }

    inout(StringValue!T)* getValue(uint vptr) inout @nogc nothrow pure {
        if (!vptr)
            return null;
        const(size_t) idx = (vptr >> POOL_BITS) - 1;
        const(size_t) off = vptr & POOL_SIZE - 1;
        return cast(inout(StringValue!T)*)&pools[idx][off];
    }

    size_t findSlot(hash_t hash, const(char)[] str) const @nogc nothrow pure {
        // quadratic probing using triangular numbers
        // http://stackoverflow.com/questions/2348187/moving-from-linear-probing-to-quadratic-probing-hash-collisons/2349774#2349774
        for (size_t i = hash & (table.length - 1), j = 1;; ++j) {
            const(StringValue!T)* sv;
            auto vptr = table[i].vptr;
            if (!vptr || table[i].hash == hash && (sv = getValue(vptr))
                    .length == str.length && .memcmp(str.ptr, sv.toDchars(), str.length) == 0)
                return i;
            i = (i + j) & (table.length - 1);
        }
    }

    void grow() nothrow pure {
        const odim = table.length;
        auto otab = table;
        const ndim = table.length * 2;
        countTrigger = (ndim * loadFactorNumerator) / loadFactorDenominator;
        table = (cast(StringEntry*) mem.xcalloc_noscan(ndim, (table[0]).sizeof))[0 .. ndim];
        foreach (const se; otab[0 .. odim]) {
            if (!se.vptr)
                continue;
            const sv = getValue(se.vptr);
            table[findSlot(se.hash, sv.toString())] = se;
        }
        mem.xfree(otab.ptr);
    }
}
