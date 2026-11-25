# Run an Inference scenario against Soroban

`infs-soroban` runs an Inference function against a local Soroban ledger. A JSON fixture declares the ledger, accounts, assets, contracts and authorized invocations. The runner reads the selected public method signatures from each compiled contract's embedded Soroban spec. It generates the Inference wrappers and host imports in a temporary directory.

## Try a token transfer

Install the [Inference compiler](https://github.com/Inferara/inference/releases/tag/v0.0.6) and put `infc` on PATH, or set `INFC_PATH` to its executable. With Rust 1.96.0, run from the repository root:

```sh
cargo install --locked --path contrib/soroban
infs-soroban contrib/soroban/examples/payment/fixture.json
```

The example starts Alice with 40 raw units in the SDK's native Stellar Asset Contract. The scenario first asks the host to transfer Alice's balance with no permission. Then it authorizes a specific transfer to Bob, calls it, checks which invocation consumed the permission and reads Bob's balance. A successful run prints `PASS transfer_balance[40]`. Edit the final assertion in [transfer.inf](examples/payment/transfer.inf) to expect zero and the same command exits with a Wasm assertion trap.

## Supply a compiled contract

Add an entry to the fixture's `contracts` array. For example, a token Wasm that publicly exports `balance(Address) -> i128` and has no constructor arguments can be registered with:

```json
{"name":"coin","wasm":"coin.wasm","constructor":[],"methods":["balance"]}
```

Paths are relative to the fixture. Constructor arguments follow the spec in order. An address argument uses the name of a fixture account, asset or previously registered contract. The entry generates `coin_balance(account: Address) -> SorobanI128`. For a struct or single-payload union result, use a `reads` entry with a local `name`, public `method`, and `path` of field or variant names. The runner checks the path against the embedded spec before compiling the scenario and checks the variant when reading the result.

`clear_auth()` removes authorized invocations. A grant in the [fixture](examples/payment/fixture.json) generates an `authorize_<name>` function taking its declared parameters as u64. Each node contains a `call` array with the contract, method and ordered arguments. Its optional `children` array describes nested authorized calls. `$name` substitutes a grant parameter. After a successful invocation, `auth_matched()` compares the signer's actual authorized invocation tree reported by the SDK with the entire selected grant. Read it before the next contract call. A generated `<contract>_rejects_<method>` executes the method and recognizes the host's outer `Context/InvalidAction` status. Other errors abort the scenario. Compare identical calls under different grants when checking authorization.

Runs in a fixture share one ledger and execute in order. Restart the command to reset the ledger. Every failed assertion exits the process with a nonzero status.

## Prototype scope

Tested with `infc` 0.0.6 and Soroban SDK 29.0.1. This companion exercises concrete examples on a local host with mock signing accounts. A universal proof would require a prover model for Soroban host calls. Credentials here exercise authorization matching and do not verify cryptographic signatures.

The boundary supports bool, i32/u32, i64/u64, Address and i128. The generated `Address` and `SorobanI128` are distinct Inference structs backed by host handles. Full i128 values can pass through contract calls. `i128_to_u64` performs a checked conversion for properties expressible with u64 arithmetic. The prototype supports one signer and one grant at a time.

Run the public end-to-end check, including its deliberately failing assertion, with:

```sh
cargo test --locked --manifest-path contrib/soroban/Cargo.toml
```
