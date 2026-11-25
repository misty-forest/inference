"""Run the public example and recompile a one-input Rust mutation in a temporary directory."""

import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def check(demo):
    spec = demo / "proof/create_lock.inf"
    original = subprocess.check_output(
        ["infs-soroban-prove", demo / "artifacts/locker.wasm", spec], text=True
    )
    for name in ("funded_lock", "unauthorized_lock"):
        assert "PROVED " + name + " " in original, original
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp)
        for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml"):
            shutil.copy(demo / name, root / name)
        shutil.copytree(demo / "src", root / "src")
        rust = root / "src/lib.rs"
        code = rust.read_text()
        old = "let lock = Lock {\n            amount,"
        assert code.count(old) == 1, "demo contract shape changed"
        rust.write_text(
            code.replace(
                old,
                "let lock = Lock {\n            amount: if amount == u64::MAX { 0 } else { amount },",
            )
        )
        subprocess.run(
            [
                "stellar",
                "contract",
                "build",
                "--locked",
                "--optimize",
                "--out-dir",
                "out",
            ],
            cwd=root,
            check=True,
        )
        result = subprocess.run(
            ["infs-soroban-prove", root / "out/inference_formal_demo.wasm", spec],
            capture_output=True,
            text=True,
        )
        assert result.returncode == 1, (result.stdout, result.stderr)
        line = next(
            line
            for line in result.stdout.splitlines()
            if line.startswith("COUNTEREXAMPLE funded_lock ")
        )
        inputs, assertion = json.JSONDecoder().raw_decode(line.split(" ", 2)[2])
        assert inputs["amount"] == 2**64 - 1 and inputs["end"] > inputs["now"], inputs
        assert 'field("amount")' in line.split(" ", 2)[2][assertion:], line
        print(original.strip())
        print(line)


if __name__ == "__main__":
    check(Path(sys.argv[1]).resolve())
