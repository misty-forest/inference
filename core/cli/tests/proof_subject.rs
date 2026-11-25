use assert_cmd::Command;
use assert_fs::TempDir;
use std::fs;

#[test]
fn sidecar_applies_the_export_of_an_unmodified_importing_module() {
    let dir = TempDir::new().unwrap();
    let src = dir.join("sidecar.inf");
    let wasm = dir.join("locker.wasm");
    fs::write(&src, "external fn lock(x: u64) -> u64; use { lock } from locker; spec Locker { fn returns_input(x: u64) forall { assert(lock(x) == x); } }").unwrap();
    let bytes = wat::parse_str(r#"(module (import "a" "0" (func (param i64))) (func (param i64) (result i64) local.get 0) (func (export "lock") (param i64) (result i64) local.get 0 call 0 local.get 0))"#).unwrap();
    fs::write(&wasm, &bytes).unwrap();
    Command::new(assert_cmd::cargo::cargo_bin!("infc"))
        .arg(src)
        .args(["--mode", "proof", "--proof-subject", "locker", "--wasm-dep"])
        .arg(format!("locker={}", wasm.display()))
        .arg("--out-dir")
        .arg(dir.path())
        .assert()
        .success();
    let v = fs::read_to_string(dir.join("sidecar.v")).unwrap();
    assert!(v.contains("T_app 1 "), "{v}");
    assert!(v.contains("ValidSpec"));
    assert!(v.contains("BI_call 0%N"));
    assert_eq!(fs::read(&wasm).unwrap(), bytes);
    assert!(!dir.join("sidecar.wasm").exists());
}

#[test]
fn soroban_auth_resolves_the_named_address_from_xdr() {
    use stellar_xdr::{
        Limits, ScSpecEntry, ScSpecFunctionInputV0, ScSpecFunctionV0, ScSpecTypeDef, ScSymbol,
        WriteXdr,
    };

    let input = |name: &str, type_| ScSpecFunctionInputV0 {
        doc: Default::default(),
        name: name.try_into().unwrap(),
        type_,
    };
    let entry = ScSpecEntry::FunctionV0(ScSpecFunctionV0 {
        doc: Default::default(),
        name: ScSymbol("lock".try_into().unwrap()),
        inputs: vec![
            input("amount", ScSpecTypeDef::U64),
            input("owner", ScSpecTypeDef::Address),
        ]
        .try_into()
        .unwrap(),
        outputs: Default::default(),
    });
    let raw = entry.to_xdr(Limits::none()).unwrap();
    let section: String = raw.iter().map(|b| format!("\\{b:02x}")).collect();
    let bytes = wat::parse_str(format!(r#"(module (@custom "contractspecv0" "{section}") (import "a" "0" (func (param i64) (result i64))) (func (export "lock") (param i64 i64) (result i64) local.get 1 call 0))"#)).unwrap();
    let dir = TempDir::new().unwrap();
    let wasm = dir.join("token.wasm");
    fs::write(&wasm, bytes).unwrap();
    let run = |request: &str| {
        Command::new(assert_cmd::cargo::cargo_bin!("infc"))
            .arg(&wasm)
            .args(["--soroban-auth", request, "--out-dir"])
            .arg(dir.path())
            .assert()
    };
    run("lock:owner").success();
    let goal = fs::read_to_string(dir.join("OwnerAuth.v")).unwrap();
    assert!(goal.contains(r#"has_call_guard contract_subject "lock"%string 1%N"#));
    assert!(!goal.contains("Admitted."));
    assert!(!goal.contains("WasmVerifier"));
    run("lock:amount")
        .failure()
        .stderr(predicates::str::contains("expects an Address"));
    run("lock:missing")
        .failure()
        .stderr(predicates::str::contains("parameter not found"));
}
