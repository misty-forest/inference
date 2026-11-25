use crate::{
    fixture::{Fixture, Grant, Host},
    interface::{method, project, Step},
};
use anyhow::{bail, ensure, Context, Result};
use soroban_sdk::{
    xdr::{ScErrorCode, ScErrorType, ScSpecTypeDef as T},
    Address, Error, IntoVal, Symbol, TryFromVal, Val, Vec as SVec,
};
use std::collections::BTreeMap;
use wasmi::{core::ValueType, Value};

fn decode<T: TryFromVal<soroban_sdk::Env, Val>>(env: &soroban_sdk::Env, v: &Val) -> Result<T> {
    T::try_from_val(env, v)
        .map_err(|e| anyhow::anyhow!("expected {}: {e:?}", std::any::type_name::<T>()))
}

#[derive(Clone, Copy)]
pub enum Scalar {
    Bool,
    U32,
    I32,
    U64,
    I64,
    Address,
    I128,
}
impl Scalar {
    fn from(t: &T) -> Result<Self> {
        Ok(match t {
            T::Bool => Self::Bool,
            T::U32 => Self::U32,
            T::I32 => Self::I32,
            T::U64 => Self::U64,
            T::I64 => Self::I64,
            T::Address => Self::Address,
            T::I128 => Self::I128,
            _ => bail!(
                "unsupported boundary type {t:?}; select a scalar field for a compound result"
            ),
        })
    }
    pub fn inf(self) -> &'static str {
        match self {
            Self::Bool => "bool",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::U64 => "u64",
            Self::U32 | Self::Address | Self::I128 => "u32",
        }
    }
    pub fn object_name(self) -> Option<&'static str> {
        match self {
            Self::Address => Some("Address"),
            Self::I128 => Some("SorobanI128"),
            _ => None,
        }
    }
    pub fn wasm(self) -> ValueType {
        match self {
            Self::U64 | Self::I64 => ValueType::I64,
            _ => ValueType::I32,
        }
    }
    fn input(self, h: &Host, v: &Value) -> Result<Val> {
        let env = &h.env;
        let i32v = || v.i32().context("expected i32");
        let i64v = || v.i64().context("expected i64");
        Ok(match self {
            Self::Bool => (i32v()? != 0).into_val(env),
            Self::U32 => (i32v()? as u32).into_val(env),
            Self::I32 => i32v()?.into_val(env),
            Self::U64 => (i64v()? as u64).into_val(env),
            Self::I64 => i64v()?.into_val(env),
            Self::Address | Self::I128 => {
                let val = *h
                    .handles
                    .get(i32v()? as u32 as usize)
                    .context("invalid object handle")?;
                match self {
                    Self::Address => {
                        decode::<Address>(env, &val)?;
                    }
                    _ => {
                        decode::<i128>(env, &val)?;
                    }
                }
                val
            }
        })
    }
    fn output(self, h: &mut Host, v: Val) -> Result<Value> {
        let env = &h.env;
        Ok(match self {
            Self::Bool => Value::I32(i32::from(decode::<bool>(env, &v)?)),
            Self::U32 => Value::I32(decode::<u32>(env, &v)? as i32),
            Self::I32 => Value::I32(decode::<i32>(env, &v)?),
            Self::U64 => Value::I64(decode::<u64>(env, &v)? as i64),
            Self::I64 => Value::I64(decode::<i64>(env, &v)?),
            Self::Address | Self::I128 => {
                let key = match self {
                    Self::Address => crate::fixture::Object::Address(decode::<Address>(env, &v)?),
                    _ => crate::fixture::Object::I128(decode::<i128>(env, &v)?),
                };
                let id = if let Some(id) = h.object_ids.get(&key) {
                    *id
                } else {
                    let id = u32::try_from(h.handles.len())?;
                    h.handles.push(v);
                    h.object_ids.insert(key, id);
                    id
                };
                Value::I32(id as i32)
            }
        })
    }
}
enum Op {
    Address(String),
    Clear,
    Grant(Grant),
    Matched,
    Narrow,
    Call {
        contract: String,
        name: String,
        path: Vec<Step>,
        rejects: bool,
    },
}
pub struct Binding {
    pub inputs: Vec<Scalar>,
    pub output: Option<Scalar>,
    op: Op,
}
pub fn identifier(name: &str) -> bool {
    let mut chars = name.chars();
    chars
        .next()
        .is_some_and(|c| c == '_' || c.is_ascii_alphabetic())
        && chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
}
impl Binding {
    pub fn all(h: &Host, f: &Fixture) -> Result<BTreeMap<String, Self>> {
        let mut b = BTreeMap::new();
        let mut add =
            |name: String, inputs: Vec<Scalar>, output: Option<Scalar>, op: Op| -> Result<()> {
                ensure!(identifier(&name), "invalid Inference identifier {name}");
                ensure!(
                    b.insert(name.clone(), Self { inputs, output, op })
                        .is_none(),
                    "duplicate generated function {name}"
                );
                Ok(())
            };
        add("clear_auth".into(), vec![], None, Op::Clear)?;
        add(
            "auth_matched".into(),
            vec![],
            Some(Scalar::Bool),
            Op::Matched,
        )?;
        add(
            "i128_to_u64".into(),
            vec![Scalar::I128],
            Some(Scalar::U64),
            Op::Narrow,
        )?;
        for n in h.names.keys() {
            add(
                n.clone(),
                vec![],
                Some(Scalar::Address),
                Op::Address(n.clone()),
            )?;
        }
        for g in &f.grants {
            ensure!(
                f.accounts.contains(&g.signer),
                "mock signer must be a fixture account"
            );
            let params: std::collections::BTreeSet<_> = g.params.iter().collect();
            ensure!(params.len() == g.params.len(), "duplicate grant parameters");
            add(
                format!("authorize_{}", g.name),
                vec![Scalar::U64; g.params.len()],
                None,
                Op::Grant(g.clone()),
            )?;
        }
        let mut register = |contract: &str,
                            alias: &str,
                            name: &str,
                            path: &[String],
                            rejects: bool|
         -> Result<()> {
            let m = method(&h.abis, contract, name)?;
            let (ty, path) = h.abis[contract].projection(m.output.clone(), path)?;
            let output = if rejects {
                Some(Scalar::Bool)
            } else if ty == T::Void {
                None
            } else {
                Some(Scalar::from(&ty)?)
            };
            let inputs = m.inputs.iter().map(Scalar::from).collect::<Result<_>>()?;
            add(
                format!("{contract}_{alias}"),
                inputs,
                output,
                Op::Call {
                    contract: contract.into(),
                    name: name.into(),
                    path,
                    rejects,
                },
            )
        };
        for a in &f.assets {
            register(&a.name, "balance", "balance", &[], false)?;
            register(&a.name, "transfer", "transfer", &[], false)?;
            register(&a.name, "rejects_transfer", "transfer", &[], true)?;
        }
        for c in &f.contracts {
            for n in &c.methods {
                register(&c.name, n, n, &[], false)?;
                register(&c.name, &format!("rejects_{n}"), n, &[], true)?;
            }
            for r in &c.reads {
                register(&c.name, &r.name, &r.method, &r.path, false)?;
            }
        }
        Ok(b)
    }
    pub fn call(&self, h: &mut Host, args: &[Value]) -> Result<Option<Value>> {
        let value = match &self.op {
            Op::Clear => {
                h.env.set_auths(&[]);
                h.expected = None;
                h.matched = false;
                return Ok(None);
            }
            Op::Matched => return Ok(Some(Value::I32(i32::from(h.matched)))),
            Op::Address(name) => h.address(name)?.to_val(),
            Op::Grant(g) => {
                let a = args
                    .iter()
                    .map(|v| {
                        v.i64()
                            .map(|i| i as u64)
                            .context("expected u64 grant parameter")
                    })
                    .collect::<Result<Vec<_>>>()?;
                h.grant(g, &a)?;
                return Ok(None);
            }
            Op::Narrow => {
                let val = Scalar::I128.input(h, &args[0])?;
                let n = decode::<i128>(&h.env, &val)?;
                return Ok(Some(Value::I64(
                    u64::try_from(n).context("i128 outside u64 range")? as i64,
                )));
            }
            Op::Call {
                contract,
                name,
                path,
                rejects,
            } => {
                let mut params = SVec::new(&h.env);
                for (k, v) in self.inputs.iter().zip(args) {
                    params.push_back(k.input(h, v)?);
                }
                let result = h.env.try_invoke_contract::<Val, Error>(
                    h.address(contract)?,
                    &Symbol::new(&h.env, name),
                    params,
                );
                h.matched = result.is_ok()
                    && h.expected
                        .as_ref()
                        .is_some_and(|e| h.env.auths().as_slice() == std::slice::from_ref(e));
                if *rejects {
                    let denied = match result {
                        Ok(Ok(_)) => false,
                        Err(Ok(e))
                            if e == Error::from_type_and_code(
                                ScErrorType::Context,
                                ScErrorCode::InvalidAction,
                            ) =>
                        {
                            true
                        }
                        other => bail!("{contract}.{name}: unexpected result {other:?}"),
                    };
                    return Ok(Some(Value::I32(i32::from(denied))));
                }
                let val = match result {
                    Ok(Ok(v)) => v,
                    other => bail!("{contract}.{name} failed: {other:?}"),
                };
                project(&h.env, val, path)?
            }
        };
        self.output.map(|o| o.output(h, value)).transpose()
    }
}
