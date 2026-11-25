use anyhow::{ensure, Context, Result};
use serde::Deserialize;
use serde_json::Value as Json;
use soroban_sdk::{
    testutils::{
        Address as _, AuthorizedInvocation, Ledger, MockAuth, MockAuthContract, MockAuthInvoke,
    },
    token, xdr, Address, Env, IntoVal, Symbol, Val, Vec as SVec,
};
use std::{collections::BTreeMap, fs, path::Path};

use crate::interface::{method, Api};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Fixture {
    pub source: String,
    pub ledger_time: u64,
    pub accounts: Vec<String>,
    #[serde(default)]
    pub assets: Vec<Asset>,
    pub contracts: Vec<Contract>,
    #[serde(default)]
    pub grants: Vec<Grant>,
    pub runs: Vec<Run>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Asset {
    pub name: String,
    pub admin: String,
    pub balances: BTreeMap<String, u64>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Contract {
    pub name: String,
    pub wasm: String,
    #[serde(default)]
    pub constructor: Vec<Json>,
    pub methods: Vec<String>,
    #[serde(default)]
    pub reads: Vec<Read>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Read {
    pub name: String,
    pub method: String,
    pub path: Vec<String>,
}
#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct Grant {
    pub name: String,
    pub signer: String,
    pub params: Vec<String>,
    pub root: Node,
}
#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct Node {
    pub call: Vec<Json>,
    #[serde(default)]
    pub children: Vec<Node>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Run {
    pub entry: String,
    pub args: Vec<u64>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub enum Object {
    Address(Address),
    I128(i128),
}

pub struct Host {
    pub env: Env,
    pub names: BTreeMap<String, Address>,
    pub abis: BTreeMap<String, Api>,
    pub object_ids: BTreeMap<Object, u32>,
    pub handles: Vec<Val>,
    pub expected: Option<(Address, AuthorizedInvocation)>,
    pub matched: bool,
}

impl Host {
    pub fn new(f: &Fixture, dir: &Path) -> Result<Self> {
        let env = Env::new_with_config(soroban_sdk::testutils::EnvTestConfig {
            capture_snapshot_at_drop: false,
        });
        env.ledger().set_timestamp(f.ledger_time);
        let mut h = Self {
            env,
            names: BTreeMap::new(),
            abis: BTreeMap::new(),
            object_ids: BTreeMap::new(),
            handles: Vec::new(),
            expected: None,
            matched: false,
        };
        for name in &f.accounts {
            let a = Address::generate(&h.env);
            h.env.register_at(&a, MockAuthContract, ());
            h.insert(name, a)?;
        }
        for asset in &f.assets {
            let admin = h.address(&asset.admin)?.clone();
            let id = h
                .env
                .register_stellar_asset_contract_v2(admin.clone())
                .address();
            h.insert(&asset.name, id.clone())?;
            h.abis.insert(asset.name.clone(), Api::token());
            for (owner, amount) in &asset.balances {
                let to = h.address(owner)?;
                let amount = i128::from(*amount);
                token::StellarAssetClient::new(&h.env, &id)
                    .mock_auths(&[MockAuth {
                        address: &admin,
                        invoke: &MockAuthInvoke {
                            contract: &id,
                            fn_name: "mint",
                            args: (to, amount).into_val(&h.env),
                            sub_invokes: &[],
                        },
                    }])
                    .mint(to, &amount);
            }
            h.env.set_auths(&[]);
        }
        for c in &f.contracts {
            let wasm =
                fs::read(dir.join(&c.wasm)).with_context(|| format!("reading {}", c.wasm))?;
            let abi = Api::from_wasm(&wasm)?;
            let types = match abi.methods.get("__constructor") {
                Some(m) => m.inputs.clone(),
                None => vec![],
            };
            let args = h.args(&types, &c.constructor, &BTreeMap::new())?;
            let address = h.env.register(wasm.as_slice(), args);
            h.insert(&c.name, address)?;
            h.abis.insert(c.name.clone(), abi);
        }
        Ok(h)
    }
    fn insert(&mut self, name: &str, a: Address) -> Result<()> {
        ensure!(
            self.names.insert(name.to_owned(), a).is_none(),
            "duplicate fixture name {name}"
        );
        Ok(())
    }
    pub fn address(&self, name: &str) -> Result<&Address> {
        self.names
            .get(name)
            .with_context(|| format!("unknown fixture address {name}"))
    }
    fn args(
        &self,
        types: &[xdr::ScSpecTypeDef],
        args: &[Json],
        vars: &BTreeMap<&str, u64>,
    ) -> Result<SVec<Val>> {
        use xdr::ScSpecTypeDef as T;
        ensure!(
            types.len() == args.len(),
            "expected {} arguments; got {}",
            types.len(),
            args.len()
        );
        let mut result = SVec::new(&self.env);
        for (ty, arg) in types.iter().zip(args) {
            let v = if let Some(key) = arg.as_str().and_then(|s| s.strip_prefix('$')) {
                Json::from(
                    *vars
                        .get(key)
                        .with_context(|| format!("unknown parameter {key}"))?,
                )
            } else {
                arg.clone()
            };
            let n = || v.as_u64().context("expected unsigned integer");
            let s = || v.as_str().context("expected string");
            let val = match ty {
                T::Address => self.address(s()?)?.to_val(),
                T::U32 => u32::try_from(n()?)?.into_val(&self.env),
                T::U64 => n()?.into_val(&self.env),
                T::I32 => i32::try_from(v.as_i64().context("expected i32")?)?.into_val(&self.env),
                T::I64 => v.as_i64().context("expected i64")?.into_val(&self.env),
                T::I128 => v
                    .as_str()
                    .map(str::to_owned)
                    .unwrap_or_else(|| v.to_string())
                    .parse::<i128>()?
                    .into_val(&self.env),
                T::Bool => v.as_bool().context("expected boolean")?.into_val(&self.env),
                T::String => soroban_sdk::String::from_str(&self.env, s()?).into_val(&self.env),
                T::Symbol => Symbol::new(&self.env, s()?).into_val(&self.env),
                _ => anyhow::bail!("unsupported fixture argument type {ty:?}"),
            };
            result.push_back(val);
        }
        Ok(result)
    }
    fn mock_call<'a>(
        &'a self,
        n: &'a Node,
        vars: &BTreeMap<&str, u64>,
    ) -> Result<MockAuthInvoke<'a>> {
        ensure!(n.call.len() >= 2, "auth call needs contract and method");
        let contract = n.call[0].as_str().context("contract name")?;
        let name = n.call[1].as_str().context("method name")?;
        let spec = method(&self.abis, contract, name)?;
        Ok(MockAuthInvoke {
            contract: self.address(contract)?,
            fn_name: name,
            args: self.args(&spec.inputs, &n.call[2..], vars)?,
            sub_invokes: &[],
        })
    }
    fn invocation(
        &self,
        n: &Node,
        vars: &BTreeMap<&str, u64>,
    ) -> Result<xdr::SorobanAuthorizedInvocation> {
        let mut node: xdr::SorobanAuthorizedInvocation = self.mock_call(n, vars)?.into();
        node.sub_invocations = n
            .children
            .iter()
            .map(|child| self.invocation(child, vars))
            .collect::<Result<Vec<_>>>()?
            .try_into()?;
        Ok(node)
    }
    pub fn grant(&mut self, g: &Grant, values: &[u64]) -> Result<()> {
        let vars = g
            .params
            .iter()
            .map(String::as_str)
            .zip(values.iter().copied())
            .collect();
        let signer = self.address(&g.signer)?.clone();
        // Let the SDK supply the signer credentials, including a fresh nonce.
        let mut entry: xdr::SorobanAuthorizationEntry = MockAuth {
            address: &signer,
            invoke: &self.mock_call(&g.root, &vars)?,
        }
        .into();
        entry.root_invocation.sub_invocations = g
            .root
            .children
            .iter()
            .map(|child| self.invocation(child, &vars))
            .collect::<Result<Vec<_>>>()?
            .try_into()?;
        self.expected = Some((
            signer,
            AuthorizedInvocation::from_xdr(&self.env, &entry.root_invocation),
        ));
        self.env.set_auths(&[entry]);
        self.matched = false;
        Ok(())
    }
}
