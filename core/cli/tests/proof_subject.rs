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

fn auth_subject(functions: &str) -> Vec<u8> {
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
    wat::parse_str(format!(
        r#"(module (@custom "contractspecv0" "{section}")
            (import "a" "0" (func $auth (param i64) (result i64)))
            {functions})"#
    ))
    .unwrap()
}

fn direct(local: u32) -> String {
    format!(r#"(func (export "lock") (param i64 i64) (result i64) local.get {local} call $auth)"#)
}

fn forwarding(helper_body: &str) -> String {
    format!(
        r#"(func $helper (param i64 i64 i64) (result i64) {helper_body})
           (func (export "lock") (param i64 i64) (result i64)
             local.get 1 i64.const 7 local.get 0 call $helper)"#
    )
}

fn chain(middle: &str, leaf: &str) -> String {
    format!(
        r#"(func $leaf (param i64 i64) (result i64) {leaf})
           (func $middle (param i64 i64 i64) (result i64) {middle})
           (func (export "lock") (param i64 i64) (result i64)
             local.get 1 i64.const 7 local.get 0 call $middle)"#
    )
}

#[test]
fn soroban_auth_resolves_the_named_address_from_xdr() {
    let bytes = auth_subject(&direct(1));
    let dir = TempDir::new().unwrap();
    let wasm = dir.join("sidecar.wasm");
    fs::write(&wasm, &bytes).unwrap();
    let src = dir.join("sidecar.inf");
    let compile = || {
        Command::new(assert_cmd::cargo::cargo_bin!("infc"))
            .arg(&src)
            .args(["--mode", "proof", "--proof-subject"])
            .arg(&wasm)
            .arg("--out-dir")
            .arg(dir.path())
            .assert()
    };
    let run = |clause: &str| {
        fs::write(&src, format!("spec Locker {{ {clause} }}")).unwrap();
        compile()
    };
    run("lock // address\n requires auth(owner);").success();
    let goal = fs::read_to_string(dir.join("sidecar.v")).unwrap();
    assert!(goal.contains(r#"AuthCertificate.certificate sidecar "lock"%string 1%nat"#));
    assert!(goal.contains(r#"requires_auth sidecar "lock"%string 1%nat"#));
    assert!(goal.contains("Theorem obligation_1_proved : obligation_1."));
    assert!(!goal.contains("Abort."));
    assert!(!goal.contains("Admitted."));
    assert_eq!(fs::read(&wasm).unwrap(), bytes);
    Command::new(assert_cmd::cargo::cargo_bin!("infc"))
        .arg(&src)
        .arg("--out-dir")
        .arg(dir.join("other"))
        .assert()
        .failure()
        .stderr(predicates::str::contains(
            "must be compiled against a Wasm proof subject",
        ));
    fs::write(&src, "external fn lock(amount:u64, owner:u64) -> u64; use { lock } from sidecar; spec Both { lock requires auth(owner); fn result(x:u64) forall { assert(lock(x,x) == x); } }").unwrap();
    compile().success();
    let mixed = fs::read_to_string(dir.join("sidecar.v")).unwrap();
    assert!(mixed.contains("ValidSpec"));
    assert!(mixed.contains("Definition obligation_1"));
    run("lock requires auth(amount);")
        .failure()
        .stderr(predicates::str::contains("expects an Address"));
    run("lock requires auth(missing);")
        .failure()
        .stderr(predicates::str::contains("parameter not found"));
    run("lock requires signed(owner);")
        .failure()
        .stderr(predicates::str::contains("expected `auth`"));
}

#[test]
#[ignore = "requires coqc and public WasmCert v2.2.0"]
fn wasmcert_checks_the_original_argument_of_the_host_call() {
    let dir = TempDir::new().unwrap();
    let spec = dir.join("sidecar.inf");
    let wasm = dir.join("contract.wasm");
    fs::write(&spec, "spec Locker { lock requires auth(owner); }").unwrap();
    for (functions, should_prove) in [
        (direct(1), true),
        (direct(0), false),
        (forwarding("local.get 0 call $auth"), true),
        (forwarding("local.get 2 call $auth"), false),
        (forwarding("i64.const 0"), false),
        (
            chain(
                "local.get 2 local.get 0 call $leaf",
                "local.get 1 call $auth",
            ),
            true,
        ),
        (
            chain(
                "local.get 0 local.get 2 call $leaf",
                "local.get 1 call $auth",
            ),
            false,
        ),
        (
            chain(
                "local.get 0 local.get 1 local.get 2 call $middle",
                "local.get 1 call $auth",
            ),
            false,
        ),
        // The helper can also return through its other branch.
        (
            forwarding("local.get 1 i64.eqz if local.get 0 call $auth return end i64.const 0"),
            false,
        ),
    ] {
        fs::write(&wasm, auth_subject(&functions)).unwrap();
        Command::new(assert_cmd::cargo::cargo_bin!("infc"))
            .arg(&spec)
            .args(["--mode", "proof", "--proof-subject"])
            .arg(&wasm)
            .arg("--out-dir")
            .arg(dir.path())
            .assert()
            .success();
        let check = Command::new("coqc")
            .current_dir(dir.path())
            .arg("sidecar.v")
            .assert();
        if should_prove {
            check.success();
        } else {
            check.failure().stderr(predicates::str::contains(
                "Cannot certify authorization of the original argument",
            ));
        }
    }
}
