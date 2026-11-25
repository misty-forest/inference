use std::{fs, path::Path, process::Command};

fn payment(fixture: &Path) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_infs-soroban"))
        .arg(fixture)
        .output()
        .unwrap()
}

#[test]
fn standard_asset_enforces_auth_and_runs_guest_assertions() {
    let dir = tempfile::tempdir().unwrap();
    let fixture = dir.path().join("fixture.json");
    let source = dir.path().join("transfer.inf");
    let scenario = include_str!("../examples/payment/transfer.inf");
    fs::write(&fixture, include_str!("../examples/payment/fixture.json")).unwrap();
    fs::write(&source, scenario).unwrap();
    let ok = payment(&fixture);
    assert!(
        ok.status.success(),
        "{}",
        String::from_utf8_lossy(&ok.stderr)
    );
    assert!(String::from_utf8_lossy(&ok.stdout).contains("PASS transfer_balance[40]"));

    fs::write(
        &source,
        scenario.replace(
            "i128_to_u64(received) == amount",
            "i128_to_u64(received) == 0",
        ),
    )
    .unwrap();
    let failed = payment(&fixture);
    assert!(!failed.status.success());
    assert!(String::from_utf8_lossy(&failed.stderr).contains("transfer_balance[40]"));
}
