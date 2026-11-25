use anyhow::{bail, ensure, Context, Result};
use soroban_sdk::{
    xdr::{ScSpecEntry, ScSpecTypeDef as T, ScSpecUdtUnionCaseV0},
    Env, Map, Symbol, TryFromVal, Val, Vec as SVec,
};
use std::collections::BTreeMap;

#[derive(Clone)]
pub struct Method {
    pub inputs: Vec<T>,
    pub output: T,
}
pub struct Api {
    pub methods: BTreeMap<String, Method>,
    entries: Vec<ScSpecEntry>,
}
pub fn method<'a>(
    abis: &'a BTreeMap<String, Api>,
    contract: &str,
    name: &str,
) -> Result<&'a Method> {
    abis.get(contract)
        .and_then(|a| a.methods.get(name))
        .with_context(|| format!("unknown public method {contract}.{name}"))
}

impl Api {
    pub fn from_wasm(wasm: &[u8]) -> Result<Self> {
        let entries = soroban_spec::read::from_wasm(wasm)?;
        let mut methods = BTreeMap::new();
        for entry in &entries {
            if let ScSpecEntry::FunctionV0(f) = entry {
                let name = f.name.to_string();
                let m = Method {
                    inputs: f.inputs.iter().map(|i| i.type_.clone()).collect(),
                    output: f.outputs.first().cloned().unwrap_or(T::Void),
                };
                ensure!(
                    methods.insert(name.clone(), m).is_none(),
                    "ambiguous method {name}"
                );
            }
        }
        ensure!(
            !methods.is_empty(),
            "missing public contract specifications"
        );
        Ok(Self { entries, methods })
    }
    // The native Stellar Asset Contract has a host implementation rather than a Wasm artifact.
    pub fn token() -> Self {
        Self {
            entries: vec![],
            methods: BTreeMap::from([
                (
                    "balance".into(),
                    Method {
                        inputs: vec![T::Address],
                        output: T::I128,
                    },
                ),
                (
                    "transfer".into(),
                    Method {
                        inputs: vec![T::Address, T::Address, T::I128],
                        output: T::Void,
                    },
                ),
            ]),
        }
    }
    pub fn projection(&self, mut ty: T, path: &[String]) -> Result<(T, Vec<Step>)> {
        let mut steps = vec![];
        for field in path {
            let T::Udt(t) = &ty else {
                bail!("cannot project {field} from {ty:?}")
            };
            let mut found = None;
            for entry in &self.entries {
                match entry {
                    ScSpecEntry::UdtStructV0(s) if s.name == t.name => {
                        if let Some(f) = s.fields.iter().find(|f| f.name.to_string() == *field) {
                            found = Some((f.type_.clone(), Step::Field(field.clone())));
                            break;
                        }
                    }
                    ScSpecEntry::UdtUnionV0(u) if u.name == t.name => {
                        for case in u.cases.iter() {
                            if let ScSpecUdtUnionCaseV0::TupleV0(c) = case {
                                if c.name.to_string() == *field && c.type_.len() == 1 {
                                    found =
                                        Some((c.type_[0].clone(), Step::Variant(field.clone())));
                                    break;
                                }
                            }
                        }
                        if found.is_some() {
                            break;
                        }
                    }
                    _ => {}
                }
            }
            let (next, step) = found.with_context(|| {
                format!(
                    "unknown field or single-value variant {field} on {}",
                    t.name
                )
            })?;
            steps.push(step);
            ty = next;
        }
        Ok((ty, steps))
    }
}
#[derive(Clone)]
pub enum Step {
    Field(String),
    Variant(String),
}
pub fn project(env: &Env, mut val: Val, steps: &[Step]) -> Result<Val> {
    for step in steps {
        val = match step {
            Step::Field(name) => Map::<Symbol, Val>::try_from_val(env, &val)
                .map_err(|e| anyhow::anyhow!("Soroban value conversion: {e:?}"))?
                .get(Symbol::new(env, name))
                .context("missing field")?,
            Step::Variant(name) => {
                let data = SVec::<Val>::try_from_val(env, &val)
                    .map_err(|e| anyhow::anyhow!("Soroban value conversion: {e:?}"))?;
                ensure!(
                    data.len() == 2
                        && Symbol::try_from_val(env, &data.get(0).context("missing tag")?)
                            .map_err(|e| anyhow::anyhow!("Soroban value conversion: {e:?}"))?
                            == Symbol::new(env, name),
                    "expected variant {name}"
                );
                data.get(1).context("missing payload")?
            }
        }
    }
    Ok(val)
}
