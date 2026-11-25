import subprocess
from pathlib import Path as File
from tempfile import TemporaryDirectory
import unittest

import z3 as z

from soroban_proof.engine import Instance, Module, Path, Trap, Unsupported, bv


class EngineTests(unittest.TestCase):
    def execute(self, wat):
        with TemporaryDirectory() as d:
            source, binary = File(d) / "probe.wat", File(d) / "probe.wasm"
            source.write_text(
                '(module (func (export "f") (param i64) (result i64) ' + wat + "))"
            )
            subprocess.run(["wat2wasm", source, "-o", binary], check=True)
            module = Module(binary)
        amount = z.BitVec("amount", 64)
        pending, results = [[]], []
        while pending:
            path = Path(pending.pop(), pending)
            try:
                result = Instance(module, path, None).invoke("f", [amount])
            except Trap:
                result = None
            results.append((path, result, amount))
        return results

    def test_rare_path_is_explored_across_full_width(self):
        paths = self.execute(
            "local.get 0 i64.const -1 i64.eq if unreachable end local.get 0"
        )
        self.assertEqual(len(paths), 2)
        for path, result, amount in paths:
            if result is None:
                self.assertFalse(path.possible(amount != bv(-1)))
            else:
                self.assertFalse(
                    path.possible(z.Or(amount == bv(-1), result != amount))
                )

    def test_branch_preserves_block_result(self):
        paths = self.execute(
            "block (result i64) i64.const 4 local.get 0 i64.eqz br_if 0 drop i64.const 8 end"
        )
        for path, result, amount in paths:
            self.assertFalse(path.possible(result != z.If(amount == 0, bv(4), bv(8))))

    def test_unsupported_operation_is_not_a_contract_rejection(self):
        with self.assertRaises(Unsupported):
            self.execute("local.get 0 i64.const 3 i64.rem_u")
