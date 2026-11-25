#!/usr/bin/env python3
"""Prove stateful Inference forall scenarios over a compiled Soroban contract."""

import argparse
from collections import Counter
import json
import os
from pathlib import Path as File
import re
import subprocess
import sys
import tempfile

import z3 as z

from .engine import Instance, Module, Path, Trap, Unsupported
from .ledger import Ledger

IDENT = r"[A-Za-z_][A-Za-z_0-9]*"
PLATFORM = {
    "proof_enter": ([], None),
    "proof_assert": (["u32", "bool"], None),
    "funded_ledger": (["u64", "u64"], None),
    "allow_transfer": (["u32", "u32", "u64"], None),
    "auth_consumed": ([], "bool"),
    "balance_u64": (["u32"], "u64"),
    "has_record": (["u32", "u32"], "bool"),
    "stored_u64": (["u32", "u32", "u32"], "u64"),
}


def interface(file):
    def info(kind):
        cmd = [
            "stellar",
            "-q",
            "contract",
            "info",
            kind,
            "--wasm",
            file,
            "--output",
            "json",
        ]
        return json.loads(subprocess.check_output(cmd))

    if info("env-meta") != [
        {"sc_env_meta_kind_interface_version": {"protocol": 29, "pre_release": 0}}
    ]:
        raise Unsupported("this profile models Soroban protocol 29")
    data = info("interface")
    methods = {}
    for entry in data:
        if "function_v0" not in entry:
            continue
        m = entry["function_v0"]
        types = [i["type_"] for i in m["inputs"]]
        if m["outputs"] or any(t not in ("u64", "address") for t in types):
            raise Unsupported(
                "supported contract signature: address/u64 inputs, void output"
            )
        if m["name"] in methods:
            raise Unsupported("duplicate contract method")
        methods[m["name"]] = types, m["outputs"]
    if not methods:
        raise Unsupported("no contract spec")
    return methods


def prelude(methods):
    functions = PLATFORM.copy()
    for name, (types, _) in methods.items():
        args = ["u32" if t == "address" else t for t in types]
        for key, ret in (
            (name, None),
            ("try_" + name, "bool"),
            ("authorize_" + name, None),
        ):
            if key in functions or not re.fullmatch(IDENT, key):
                raise Unsupported("ambiguous or invalid generated name " + key)
            functions[key] = args, ret
    lines = []
    for name, (args, res) in functions.items():
        params = ", ".join(f"a{i}: {t}" for i, t in enumerate(args))
        lines.append(
            f"external fn {name}({params})" + (f" -> {res}" if res else "") + ";"
        )
    lines += ["use { " + ", ".join(functions) + " } from host::soroban;"]
    return "\n".join(lines) + "\n"


def block(s):
    if not s.startswith("{"):
        raise Unsupported("expected a braced block")
    depth = 0
    for i, c in enumerate(s):
        depth += (c == "{") - (c == "}")
        if not depth:
            return s[1:i], s[i + 1 :].strip()
    raise Unsupported("unterminated block")


def prepare(file, methods, temp):
    text = re.sub(r"//[^\n]*", "", file.read_text()).strip()
    if "/*" in text:
        raise Unsupported("only line comments are supported in scenario sources")
    fields, assertions = [], []

    def expand(src):
        def symbol(match):
            if match[1] not in fields:
                fields.append(match[1])
            return str(fields.index(match[1]))

        src = re.sub(r'\bfield\(\s*"(' + IDENT + r')"\s*\)', symbol, src)
        return re.sub(
            r"\b(OWNER|TOKEN|LOCKER)\b",
            lambda m: {"OWNER": "0", "TOKEN": "1", "LOCKER": "2"}[m[0]],
            src,
        )

    prefix = prelude(methods)
    match = re.match(r"spec\s+" + IDENT + r"\s*", text)
    if not match:
        raise Unsupported("expected a spec block")
    content, tail = block(text[match.end() :])
    if tail:
        raise Unsupported("expected one spec block")
    source = temp / "scenario.inf"
    infc = os.environ.get("INFC_PATH", "infc")
    source.write_text(prefix + expand(text))

    def compile_phase(*args):
        proc = subprocess.run(
            [infc, source, *args],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        if proc.returncode:
            raise Unsupported(proc.stdout.strip())

    compile_phase("--analyze")
    functions, obligations = [], {}
    content = content.strip()
    while content:
        head = re.match(r"fn\s+(" + IDENT + r")\s*\(([^()]*)\)\s*forall\s*", content)
        if not head:
            raise Unsupported("only forall functions are supported")
        name, signature = head.groups()
        body, content = block(content[head.end() :])
        body = body.strip()
        params = []
        for arg in signature.split(",") if signature.strip() else []:
            p = re.fullmatch(r"\s*(" + IDENT + r")\s*:\s*(bool|u64|u32)\s*", arg)
            if not p:
                raise Unsupported("unsupported quantified parameter " + arg)
            params.append(p.groups())
        guards = []
        if re.match(r"assume\b", body):
            conditions, body = block(body[6:].lstrip())
            conditions = conditions.strip()
            while conditions:
                cond = re.match(r"assert\s*\(([^;{}]+)\)\s*;\s*", conditions)
                if not cond or re.search(IDENT + r"\s*\(", cond[1]):
                    raise Unsupported("use pure scalar guards in assume")
                guards.append("if !(" + cond[1] + ") { return; }")
                conditions = conditions[cond.end() :]
        if re.search(
            r"\b(assume|proof_enter|proof_assert|forall|exists|return|ndet)\b|@", body
        ):
            raise Unsupported("unsupported control flow in a forall scenario")
        if name in obligations or not re.search(r"\bassert\s*\(", body):
            raise Unsupported("duplicate name or missing assertion")

        def label(m):
            assertions.append(m[1].strip())
            return f"proof_assert({len(assertions) - 1}, {m[1]});"

        body = re.sub(r"\bassert\s*\(([^;{}]+)\)\s*;", label, body)
        if re.search(r"\bassert\s*\(", body):
            raise Unsupported("unrecognized assertion")
        obligations[name] = params
        functions.append(
            f"pub fn {name}({signature}) {{"
            + "\n".join(guards)
            + "\nproof_enter();\n"
            + body
            + "}"
        )
    if not obligations:
        raise Unsupported("empty spec")
    source.write_text(prefix + expand("\n".join(functions)))
    compile_phase("--mode", "compile", "--out-dir", temp)
    return Module(temp / "scenario.wasm"), obligations, fields, assertions


def check(name, params, contract, scenario, methods, fields, assertions):
    symbols = {p: z.BitVec(p, 64 if t == "u64" else 32) for p, t in params}
    pending, outcomes = [[]], Counter()
    while pending:
        if sum(outcomes.values()) >= 4096:
            raise Unsupported("path budget exceeded")
        path = Path(pending.pop(), pending)
        for p, t in params:
            if t == "bool":
                path.solver.add(z.ULE(symbols[p], 1))
        ledger = Ledger(contract, path, methods, fields, assertions)
        try:
            Instance(scenario, path, ledger.binding).invoke(
                name, list(symbols.values())
            )
        except Trap as error:
            if not path.possible(z.BoolVal(True)):
                raise Unsupported("inconsistent counterexample")
            model = path.solver.model()
            values = {
                p: model.eval(v, model_completion=True).as_long()
                for p, v in symbols.items()
            }
            print("COUNTEREXAMPLE", name, json.dumps(values), str(error), flush=True)
            return False
        if ledger.reached and not ledger.asserted:
            raise Unsupported("admitted path without an assertion: " + name)
        outcomes["admitted" if ledger.reached else "excluded"] += 1
    if not outcomes["admitted"]:
        raise Unsupported("unsatisfiable preconditions: " + name)
    print(f"PROVED {name} ({outcomes['admitted']} admitted symbolic paths)", flush=True)
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("wasm", type=File)
    parser.add_argument("spec", type=File)
    args = parser.parse_args()
    methods = interface(args.wasm)
    contract = Module(args.wasm)
    with tempfile.TemporaryDirectory() as temp:
        scenario, obligations, fields, assertions = prepare(
            args.spec, methods, File(temp)
        )
        for name, params in obligations.items():
            if not check(name, params, contract, scenario, methods, fields, assertions):
                return 1
    return 0


def cli():
    try:
        return main()
    except (
        Unsupported,
        KeyError,
        IndexError,
        ValueError,
        OSError,
        RecursionError,
        subprocess.CalledProcessError,
    ) as error:
        print("INCONCLUSIVE: " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(cli())
