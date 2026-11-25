//! Resolve the public Soroban ABI and emit a closed-shape Rocq goal over its Wasm.
use anyhow::{Context, Result, ensure};
use std::{fmt::Write as _, fs, io::Cursor, path::Path};
use stellar_xdr::{Limited, Limits, ReadXdr, ScSpecEntry, ScSpecTypeDef};
use wasmparser::{Parser, Payload, Validator};

fn address_parameter(bytes: &[u8], export: &str, parameter: &str) -> Result<usize> {
    let mut spec = None;
    for payload in Parser::new(0).parse_all(bytes) {
        if let Payload::CustomSection(section) = payload?
            && section.name() == "contractspecv0"
        {
            ensure!(
                spec.replace(section.data()).is_none(),
                "ambiguous contractspecv0 section"
            );
        }
    }
    let raw = spec.context("missing Soroban contractspecv0")?;
    let mut reader = Limited::new(
        Cursor::new(raw),
        Limits {
            depth: 500,
            len: raw.len(),
        },
    );
    let mut argument = None;
    for entry in ScSpecEntry::read_xdr_iter(&mut reader) {
        if let ScSpecEntry::FunctionV0(f) = entry?
            && f.name.0.as_slice() == export.as_bytes()
        {
            ensure!(argument.is_none(), "duplicate function in contractspecv0");
            let mut matches = f
                .inputs
                .iter()
                .enumerate()
                .filter(|(_, i)| i.name.as_slice() == parameter.as_bytes());
            let (index, input) = matches
                .next()
                .context("parameter not found in contractspecv0")?;
            ensure!(matches.next().is_none(), "ambiguous parameter name");
            ensure!(
                input.type_ == ScSpecTypeDef::Address,
                "require_auth expects an Address parameter"
            );
            argument = Some(index);
        }
    }
    argument.context("export not found in contractspecv0")
}

pub(super) fn generate(path: &Path, request: &str, out: Option<&Path>) -> Result<()> {
    let (export, parameter) = request.split_once(':').context("expected EXPORT:PARAM")?;
    ensure!(
        [export, parameter]
            .iter()
            .all(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')),
        "invalid Soroban symbol"
    );
    let bytes = fs::read(path)?;
    Validator::new().validate_all(&bytes)?;
    let index = address_parameter(&bytes, export, parameter)?;
    let mut proof = inference::translate_subject_module(&bytes)?;
    proof.push_str(include_str!("../../wasm-to-v/rocq/CallGuard.v"));
    writeln!(
        proof,
        "\nTheorem owner_auth : has_call_guard contract_subject \"{export}\"%string {index}%N \"a\"%string \"0\"%string."
    )?;
    proof.push_str("Proof. prove_call_guard. Qed.\n");
    let dir = out.unwrap_or(Path::new("out"));
    fs::create_dir_all(dir)?;
    let output = dir.join("OwnerAuth.v");
    fs::write(&output, proof)?;
    println!(
        "Rocq goal generated at {}. Run coqc to check the guard.",
        output.display()
    );
    Ok(())
}
