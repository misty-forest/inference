//! Bind source authorization clauses to Soroban ABI parameters and WasmCert obligations.
use anyhow::{Context, Result, ensure};
use std::{fmt::Write as _, io::Cursor};
use stellar_xdr::{Limited, Limits, ReadXdr, ScSpecEntry, ScSpecFunctionV0, ScSpecTypeDef};
use wasmparser::{Parser, Payload, Validator};

fn functions(bytes: &[u8]) -> Result<Vec<ScSpecFunctionV0>> {
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
    let mut functions = Vec::new();
    for entry in ScSpecEntry::read_xdr_iter(&mut reader) {
        if let ScSpecEntry::FunctionV0(function) = entry? {
            functions.push(function);
        }
    }
    Ok(functions)
}

fn address_parameter(
    functions: &[ScSpecFunctionV0],
    types: wasmparser::types::TypesRef<'_>,
    export: &str,
    parameter: &str,
) -> Result<usize> {
    let mut matches = functions
        .iter()
        .filter(|f| f.name.0.as_slice() == export.as_bytes());
    let f = matches
        .next()
        .context("export not found in contractspecv0")?;
    ensure!(
        matches.next().is_none(),
        "duplicate function in contractspecv0"
    );
    let ty = types
        .core_exports()
        .and_then(|mut exports| exports.find(|(name, _)| *name == export));
    let Some((_, wasmparser::types::EntityType::Func(id))) = ty else {
        anyhow::bail!("contractspecv0 function has no matching Wasm function export");
    };
    let signature = types[id].unwrap_func();
    ensure!(
        signature.params().len() == f.inputs.len()
            && signature
                .params()
                .iter()
                .all(|p| *p == wasmparser::ValType::I64)
            && signature.results() == [wasmparser::ValType::I64],
        "Wasm export disagrees with the Soroban Val ABI"
    );
    let mut inputs = f
        .inputs
        .iter()
        .enumerate()
        .filter(|(_, i)| i.name.as_slice() == parameter.as_bytes());
    let (slot, input) = inputs
        .next()
        .context("parameter not found in contractspecv0")?;
    ensure!(inputs.next().is_none(), "ambiguous parameter name");
    ensure!(
        input.type_ == ScSpecTypeDef::Address,
        "require_auth expects an Address parameter"
    );
    Ok(slot)
}

pub(super) fn append_requirements(
    proof: &mut String,
    module: &str,
    bytes: &[u8],
    clauses: &[(String, String)],
) -> Result<()> {
    if clauses.is_empty() {
        return Ok(());
    }
    let types = Validator::new().validate_all(bytes)?;
    let functions = functions(bytes)?;
    proof.push_str(include_str!("../rocq/CallGuard.v"));
    proof.push_str(include_str!("../rocq/Authorization.v"));
    proof.push_str(concat!(
        include_str!("../rocq/AuthEntry.v"),
        include_str!("../rocq/AuthTraps.v"),
        include_str!("../rocq/AuthOuter.v"),
        include_str!("../rocq/AuthStore.v"),
        include_str!("../rocq/GuardedExecution.v"),
        include_str!("../rocq/AuthInvocation.v"),
        include_str!("../rocq/AuthResolve.v"),
        include_str!("../rocq/AuthSound.v"),
        include_str!("../rocq/AuthForward.v"),
        include_str!("../rocq/AuthCallContext.v"),
        include_str!("../rocq/AuthForwardSound.v"),
        include_str!("../rocq/AuthCertificate.v"),
    ));
    for (i, (export, parameter)) in clauses.iter().enumerate() {
        let slot = address_parameter(&functions, types.as_ref(), export, parameter)
            .with_context(|| format!("resolving {export} requires auth({parameter})"))?;
        let export = crate::gallina::escape_string_literal(export);
        let n = i + 1;
        writeln!(
            proof,
            "\nDefinition obligation_{n} : Prop := requires_auth {module} \"{export}\"%string {slot}%nat."
        )?;
        writeln!(
            proof,
            "Theorem guard_{n} : AuthCertificate.certificate {module} \"{export}\"%string {slot}%nat.\nProof. AuthCertificate.prove_certificate. Qed."
        )?;
        writeln!(
            proof,
            "Theorem obligation_{n}_proved : obligation_{n}.\nProof. exact (AuthCertificate.sound _ _ _ guard_{n}). Qed."
        )?;
    }
    Ok(())
}
