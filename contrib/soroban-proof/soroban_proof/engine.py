"""Path exploration with exact Wasm bitvectors. Unsupported operations fail closed."""

import re
import subprocess

import z3 as z


class Unsupported(Exception):
    pass


class Trap(Exception):
    """A runtime trap in a supported Wasm/host operation."""


def bv(value, width=64):
    return z.BitVecVal(value, width)


def boolean(condition):
    return z.If(condition, bv(1, 32), bv(0, 32))


class Path:
    def __init__(self, decisions, pending):
        self.solver = z.Solver()
        self.solver.set(timeout=15000)
        self.decisions, self.pending, self.chosen = decisions, pending, []

    def possible(self, condition):
        result = self.solver.check(condition)
        if result == z.unknown:
            raise Unsupported(self.solver.reason_unknown())
        return result == z.sat

    def branch(self, cond):
        cond = z.simplify(cond)
        if z.is_true(cond) or z.is_false(cond):
            return z.is_true(cond)
        yes, no = self.possible(cond), self.possible(z.Not(cond))
        if not yes and not no:
            raise Unsupported("inconsistent execution path")
        if yes and no:
            i = len(self.chosen)
            if i < len(self.decisions):
                yes = self.decisions[i]
            else:
                self.pending.append(self.chosen + [False])
            self.chosen.append(yes)
        self.solver.add(cond if yes else z.Not(cond))
        return yes

    def number(self, expr):
        expr = z.simplify(expr)
        if z.is_bv_value(expr):
            return expr.as_long()
        if not self.possible(z.BoolVal(True)):
            raise Unsupported("inconsistent execution path")
        value = self.solver.model().eval(expr, model_completion=True)
        if self.possible(expr != value):
            raise Unsupported("non-unique memory address, symbol or object handle")
        return value.as_long()


def sexpr(wat):
    # wasm2wat emits indexed, unfolded WAT when called with --no-debug-names.
    tokens = re.findall(
        r'\(;.*?;\)|;;[^\n]*|"(?:\\.|[^"\\])*"|[()]|[^\s()"]+', wat, re.S
    )
    stack = [[]]
    for token in tokens:
        if token.startswith((";;", "(;")):
            continue
        if token == "(":
            stack.append([])
        elif token == ")":
            node = stack.pop()
            stack[-1].append(node)
        else:
            stack[-1].append(token)
    return stack[0][0]


def literal(text):
    value = bytearray()
    s = text[1:-1]
    i = 0
    while i < len(s):
        if s[i] == "\\":
            if re.match("[0-9a-fA-F]{2}", s[i + 1 : i + 3]):
                value.append(int(s[i + 1 : i + 3], 16))
                i += 3
                continue
            value.append({"n": 10, "t": 9, "r": 13, '"': 34, "\\": 92}[s[i + 1]])
            i += 2
        else:
            value.extend(s[i].encode())
            i += 1
    return bytes(value)


def instructions(items):
    root, blocks = [], []
    current = root
    i = 0
    while i < len(items):
        op = items[i]
        i += 1
        if op in ("block", "loop", "if"):
            arity = 0
            if i < len(items) and isinstance(items[i], list):
                if items[i] not in (["result", "i64"], ["result", "i32"]):
                    raise Unsupported("block type")
                arity, i = 1, i + 1
            yes, no = [], []
            current.append((op, (arity, yes, no)))
            blocks.append((current, no))
            current = yes
        elif op == "else":
            current = blocks[-1][1]
        elif op == "end":
            current = blocks.pop()[0]
        elif op in (
            "br",
            "br_if",
            "call",
            "local.get",
            "local.set",
            "local.tee",
            "global.get",
            "global.set",
            "i32.const",
            "i64.const",
        ):
            current.append((op, int(items[i])))
            i += 1
        elif re.fullmatch(
            r"i(?:32|64)\.(?:load|store)(?:8_[us]|8|16_[us]|16|32_[us]|32)?", op
        ):
            offset = 0
            while (
                i < len(items)
                and isinstance(items[i], str)
                and items[i].startswith(("offset=", "align="))
            ):
                if items[i].startswith("offset="):
                    offset = int(items[i][7:])
                i += 1
            current.append((op, offset))
        else:
            current.append((op, None))
    if blocks:
        raise Unsupported("unclosed block")
    return root


class Module:
    def __init__(self, file):
        tree = sexpr(
            subprocess.check_output(["wasm2wat", "--no-debug-names", file], text=True)
        )
        self.funcs, self.types, self.globals, self.data, self.exports = (
            [],
            [],
            [],
            [],
            {},
        )
        self.pages = 0
        memory_seen = False
        for item in tree[1:]:
            kind, *args = item
            if kind == "type":
                params, results = [], []
                for group in args[0][1:]:
                    {"param": params, "result": results}[group[0]].extend(group[1:])
                if (
                    any(t not in ("i32", "i64") for t in params + results)
                    or len(results) > 1
                ):
                    raise Unsupported("function type")
                self.types.append((params, results))
            elif kind == "import":
                mod, name, desc = args
                if desc[0] != "func":
                    raise Unsupported("non-function import")
                self.funcs.append(
                    (int(desc[1][1]), (), (mod.strip('"'), name.strip('"')))
                )
            elif kind == "func":
                ty = int(args.pop(0)[1])
                locals_ = []
                while args and isinstance(args[0], list):
                    group = args.pop(0)
                    if group[0] == "local":
                        locals_.extend(group[1:])
                    elif group[0] not in ("param", "result"):
                        raise Unsupported(group)
                self.funcs.append((ty, locals_, instructions(args)))
            elif kind == "export":
                if args[1][0] == "func":
                    self.exports[args[0].strip('"')] = int(args[1][1])
            elif kind == "memory":
                if (
                    memory_seen
                    or len(args) not in (1, 2)
                    or not all(v.isdigit() for v in args)
                ):
                    raise Unsupported("only one unshared memory32 is supported")
                memory_seen = True
                self.pages = int(args[0])
            elif kind == "global":
                op, n = args[-1]
                if op not in ("i32.const", "i64.const"):
                    raise Unsupported(op)
                self.globals.append(bv(int(n), int(op[1:3])))
            elif kind == "data":
                if args[0][0] != "i32.const":
                    raise Unsupported("data offset")
                self.data.append((int(args[0][1]), b"".join(map(literal, args[1:]))))
            else:
                raise Unsupported(f"unsupported Wasm section {kind}")

        if any(p < 0 or p + len(data) > self.pages * 65536 for p, data in self.data):
            raise Unsupported("data segment outside initial memory")


class Jump(Exception):
    def __init__(self, depth):
        self.depth = depth


class Return(Exception):
    pass


class Instance:
    def __init__(self, module, path, host):
        self.m, self.path, self.host = module, path, host
        self.globals = module.globals.copy()
        self.memory = {
            p + i: bv(b, 8) for p, data in module.data for i, b in enumerate(data)
        }
        self.steps = 0

    def bounds(self, p, n):
        if not 0 <= p <= self.m.pages * 65536 - n:
            raise Trap("memory bounds")

    def load(self, p, n):
        self.bounds(p, n)
        values = [self.memory.get(p + i, bv(0, 8)) for i in reversed(range(n))]
        return z.simplify(z.Concat(*values) if n > 1 else values[0])

    def store(self, p, n, v):
        self.bounds(p, n)
        for i in range(n):
            self.memory[p + i] = z.simplify(z.Extract(i * 8 + 7, i * 8, v))

    def call(self, index, args):
        ty, locals_, body = self.m.funcs[index]
        params, results = self.m.types[ty]
        if [v.size() for v in args] != [int(t[1:]) for t in params]:
            raise Unsupported("call signature")
        if isinstance(body, tuple):
            result = self.host(self, *body, *args)
        else:
            loc = list(args) + [bv(0, int(t[1:])) for t in locals_]
            stack = []
            try:
                self.execute(body, loc, stack)
            except Return:
                pass
            except Jump as jump:
                if jump.depth != 0:
                    raise Unsupported("invalid branch")
            result = stack[-1] if results else None
        if (result is None) != (not results) or (
            results and result.size() != int(results[0][1:])
        ):
            raise Unsupported("result signature")
        return result

    def invoke(self, name, args):
        return self.call(self.m.exports[name], args)

    def execute(self, code, loc, s):
        for op, arg in code:
            self.steps += 1
            if self.steps > 100000:
                raise Unsupported("instruction budget exceeded")
            if op in ("block", "loop", "if"):
                arity, yes, no = arg
                body = no if op == "if" and not self.path.branch(s.pop() != 0) else yes
                height = len(s)
                while True:
                    try:
                        self.execute(body, loc, s)
                    except Jump as jump:
                        if jump.depth:
                            jump.depth -= 1
                            raise
                        keep = 0 if op == "loop" else arity
                        s[height:] = s[-keep:] if keep else []
                        if op == "loop":
                            continue
                    break
            elif op == "br" or (op == "br_if" and self.path.branch(s.pop() != 0)):
                raise Jump(arg)
            elif op in ("br_if", "nop"):
                pass
            elif op == "unreachable":
                raise Trap("Wasm unreachable")
            elif op == "return":
                raise Return()
            elif op == "drop":
                s.pop()
            elif op == "select":
                cond, b, a = s.pop(), s.pop(), s.pop()
                s.append(z.If(cond != 0, a, b))
            elif op == "call":
                n = len(self.m.types[self.m.funcs[arg][0]][0])
                result = self.call(arg, [s.pop() for _ in range(n)][::-1])
                if result is not None:
                    s.append(result)
            elif op == "local.get":
                s.append(loc[arg])
            elif op == "local.set":
                loc[arg] = s.pop()
            elif op == "local.tee":
                loc[arg] = s[-1]
            elif op == "global.get":
                s.append(self.globals[arg])
            elif op == "global.set":
                self.globals[arg] = s.pop()
            elif op in ("i32.const", "i64.const"):
                s.append(bv(arg, int(op[1:3])))
            elif op in ("i32.wrap_i64", "i64.extend_i32_u", "i64.extend_i32_s"):
                a = s.pop()
                s.append(
                    z.Extract(31, 0, a)
                    if op == "i32.wrap_i64"
                    else z.ZeroExt(32, a)
                    if op.endswith("_u")
                    else z.SignExt(32, a)
                )
            elif op.startswith(("i32.load", "i64.load", "i32.store", "i64.store")):
                width = int(op[1:3])
                m = re.search(r"(?:load|store)(8|16|32)", op)
                bits = int(m[1]) if m else width
                if ".store" in op:
                    value = s.pop()
                    self.store(self.path.number(s.pop()) + arg, bits // 8, value)
                else:
                    val = self.load(self.path.number(s.pop()) + arg, bits // 8)
                    s.append(
                        (z.SignExt if op.endswith("_s") else z.ZeroExt)(
                            width - bits, val
                        )
                    )
            elif op in ("i32.eqz", "i64.eqz"):
                s.append(boolean(s.pop() == 0))
            elif op.startswith(("i32.", "i64.")):
                b, a = s.pop(), s.pop()
                shift = b & (a.size() - 1)
                operations = {
                    "add": lambda: a + b,
                    "sub": lambda: a - b,
                    "mul": lambda: a * b,
                    "and": lambda: a & b,
                    "or": lambda: a | b,
                    "xor": lambda: a ^ b,
                    "shl": lambda: a << shift,
                    "shr_s": lambda: a >> shift,
                    "shr_u": lambda: z.LShR(a, shift),
                    "eq": lambda: a == b,
                    "ne": lambda: a != b,
                    "lt_u": lambda: z.ULT(a, b),
                    "gt_u": lambda: z.UGT(a, b),
                    "le_u": lambda: z.ULE(a, b),
                    "ge_u": lambda: z.UGE(a, b),
                    "lt_s": lambda: a < b,
                    "gt_s": lambda: a > b,
                    "le_s": lambda: a <= b,
                    "ge_s": lambda: a >= b,
                }
                if op[4:] not in operations:
                    raise Unsupported(op)
                result = operations[op[4:]]()
                s.append(z.simplify(boolean(result) if z.is_bool(result) else result))
            else:
                raise Unsupported(op)
