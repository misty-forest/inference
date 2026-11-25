"""Symbolic fresh ledger and a standard asset, scoped to the documented host subset."""

import z3 as z

from .engine import Instance, Trap, Unsupported, boolean, bv

OWNER, TOKEN, LOCKER = 0, 1, 2
VOID = bv(2)


def small_symbol(name):
    alphabet = "_0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
    body = 0
    for c in name:
        body = body * 64 + alphabet.index(c) + 1
    return (body << 8) | 14


class Ledger:
    def __init__(self, module, path, methods, symbols, assertions):
        self.module, self.path, self.methods, self.symbols = (
            module,
            path,
            methods,
            symbols,
        )
        self.assertions = assertions
        self.ready = False
        self.reached = False
        self.asserted = False

    def reset(self, now, funds):
        if self.ready:
            raise Unsupported("one initial ledger per scenario")
        self.ready, self.clock, self.invoked = True, now, False
        self.balances = {OWNER: z.ZeroExt(64, funds), LOCKER: bv(0, 128)}
        self.storage = {}
        self.grant = self.child = None
        self.root_used = self.child_used = False

    def require(self, condition, reason):
        if not self.path.branch(condition):
            raise Trap(reason)

    def obj(self, tag, value):
        word = (len(self.objects) << 33) | tag
        self.objects[word] = value
        return bv(word)

    def get(self, value, tag):
        word = self.path.number(value)
        if word & 255 != tag or word not in self.objects:
            raise Trap("invalid host object")
        return self.objects[word]

    def pack64(self, number):
        if self.path.branch(z.ULE(number, (1 << 56) - 1)):
            return (number << 8) | 6
        return self.obj(64, number)

    def unpack64(self, word):
        if self.path.branch((word & 255) == 6):
            return z.LShR(word, 8)
        return self.get(word, 64)

    def unpack128(self, word):
        if self.path.branch((word & 255) == 11):
            return z.SignExt(64, word >> 8)
        return self.get(word, 69)

    def addr(self, word):
        return self.get(word, 77)

    def key(self, word):
        # The storage profile uses Vec<Address> keys. Other shapes are inconclusive.
        if self.path.number(word & 255) != 75:
            raise Unsupported("only vector storage keys are modeled")
        items = self.get(word, 75)
        if any(self.path.number(v & 255) != 77 for v in items):
            raise Unsupported("only address components in storage keys are modeled")
        return tuple(self.addr(v) for v in items)

    def transfer(self, target, method, args):
        if (target, method) != (TOKEN, small_symbol("transfer")):
            raise Unsupported("only standard-asset transfer is modeled")
        if len(args) != 3:
            raise Trap("transfer arity")
        sender, recipient = map(self.addr, args[:2])
        if (sender, recipient) != (OWNER, LOCKER):
            raise Unsupported("only owner-to-locker transfers are modeled")
        value = self.unpack128(args[2])
        if not self.root_used or self.child_used or self.child is None:
            raise Trap("missing nested transfer grant")
        sender_ok, recipient_ok, approved = self.child
        if (sender, recipient) != (sender_ok, recipient_ok):
            raise Trap("transfer grant addresses")
        self.require(value == z.ZeroExt(64, approved), "transfer grant amount")
        if sender not in self.balances or recipient not in self.balances:
            raise Unsupported("asset address outside the funded-ledger profile")
        self.require(
            z.And(value >= 0, self.balances[sender] >= value), "insufficient balance"
        )
        self.balances[sender] -= value
        self.require(
            self.balances[recipient] <= bv((1 << 127) - 1, 128) - value,
            "balance overflow",
        )
        self.balances[recipient] += value
        self.child_used = True
        return VOID

    def host(self, vm, mod, name, *a):
        op = (mod, name)
        num = self.path.number

        def u32(word):
            n = num(word)
            if n & 0xFFFFFFFF != 4:
                raise Trap("invalid U32Val")
            return n >> 32

        if op == ("i", "0"):
            return self.get(a[0], 64)
        if op == ("i", "_"):
            return self.obj(64, a[0])
        if op == ("i", "6"):
            return self.obj(69, z.Concat(*a))
        if op == ("x", "4"):
            return self.pack64(self.clock)
        if op == ("x", "7"):
            return self.obj(77, LOCKER)
        if op == ("a", "0"):
            if self.grant is None or self.addr(a[0]) != OWNER:
                raise Trap("missing owner authorization")
            method, expected = self.grant
            if method != self.method:
                raise Trap("wrong authorized function")
            self.require(
                z.And(*[x == y for x, y in zip(self.args, expected, strict=True)]),
                "wrong authorized arguments",
            )
            self.root_used = True
            return VOID
        if op == ("v", "g"):
            p, n = map(u32, a)
            if n > 256:
                raise Unsupported("vector size")
            return self.obj(75, [vm.load(p + i * 8, 8) for i in range(n)])
        if op == ("m", "9"):
            kp, vp, n = map(u32, a)
            if n > 256:
                raise Unsupported("map size")
            fields = {}
            for i in range(n):
                addr, size = (num(vm.load(kp + 8 * i + k, 4)) for k in (0, 4))
                if size > 32:
                    raise Trap("symbol length")
                field = bytes(num(vm.load(addr + k, 1)) for k in range(size)).decode(
                    "ascii"
                )
                if fields and field <= next(reversed(fields)):
                    raise Trap("map key order")
                fields[field] = vm.load(vp + 8 * i, 8)
            return self.obj(76, fields)
        if op in (("l", "0"), ("l", "_")):
            key = (num(a[-1]), self.key(a[0]))
            if key[0] not in (0, 1):
                raise Unsupported("storage durability")
            if op == ("l", "0"):
                return bv(int(key in self.storage))
            # Store logical field values, independent of this invocation's handle table.
            if num(a[1] & 255) != 76:
                raise Unsupported("only record values in storage are modeled")
            if any(num(v & 255) not in (6, 64) for v in self.get(a[1], 76).values()):
                raise Unsupported("only u64 fields in storage records are modeled")
            self.storage[key] = {
                k: self.unpack64(v) for k, v in self.get(a[1], 76).items()
            }
            return VOID
        if op == ("d", "_"):
            return self.transfer(self.addr(a[0]), num(a[1]), self.get(a[2], 75))
        raise Unsupported(f"unmodeled Soroban import {mod}::{name}")

    def invoke(self, method, args, catch):
        if self.invoked:
            raise Unsupported("one contract invocation per fresh ledger")
        self.invoked = True
        types, result = self.methods[method]
        self.objects = {}
        self.method, self.args = method, args
        self.root_used = self.child_used = False
        packed = [
            self.obj(77, self.path.number(v)) if t == "address" else self.pack64(v)
            for t, v in zip(types, args, strict=True)
        ]
        balances, storage = self.balances.copy(), self.storage.copy()
        try:
            value = Instance(self.module, self.path, self.host).invoke(method, packed)
            if result:
                raise Unsupported("only void contract methods in this profile")
            self.require(value == VOID, "invalid void return")
        except Trap:
            self.balances, self.storage = balances, storage
            self.root_used = self.child_used = False
            if catch:
                return bv(0, 32)
            raise
        return bv(1, 32) if catch else None

    def binding(self, vm, mod, name, *args):
        if mod != "soroban":
            raise Unsupported(f"unknown proof module {mod}")
        if name == "proof_enter":
            self.reached = True
            return
        if name == "funded_ledger":
            self.reset(*args)
            return
        if name == "proof_assert":
            self.asserted = True
            self.require(
                args[1] != 0,
                "assert(" + self.assertions[self.path.number(args[0])] + ")",
            )
            return
        if not self.ready:
            raise Unsupported("initialize funded_ledger first")
        if name in self.methods:
            return self.invoke(name, args, False)
        if name.startswith("try_") and name[4:] in self.methods:
            return self.invoke(name[4:], args, True)
        if name.startswith("authorize_") and name[10:] in self.methods:
            if self.grant is not None:
                raise Unsupported("one root grant per fixture")
            self.grant = name[10:], args
            return
        num = self.path.number
        if name == "allow_transfer":
            if self.grant is None or self.child is not None:
                raise Unsupported("one transfer child on a root grant")
            self.child = num(args[0]), num(args[1]), args[2]
        elif name == "auth_consumed":
            return boolean(
                z.BoolVal(
                    self.grant is not None
                    and self.root_used
                    and (self.child is None or self.child_used)
                )
            )
        elif name == "balance_u64":
            value = self.balances[num(args[0])]
            self.require(z.ULE(value, (1 << 64) - 1), "balance outside u64")
            return z.Extract(63, 0, value)
        elif name in ("has_record", "stored_u64"):
            record = self.storage.get((1, (num(args[0]), num(args[1]))))
            if name == "has_record":
                return boolean(z.BoolVal(record is not None))
            field = self.symbols[num(args[2])]
            if record is None or field not in record:
                raise Trap("missing persistent field: " + field)
            return record[field]
        else:
            raise Unsupported("unknown proof binding " + name)
