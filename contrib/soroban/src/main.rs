mod bindings;
mod fixture;
mod interface;

use anyhow::{bail, ensure, Context, Result};
use bindings::Binding;
use fixture::{Fixture, Host};
use std::{
    collections::BTreeMap,
    env,
    ffi::OsString,
    fmt::Write as _,
    fs,
    path::{Path, PathBuf},
    process::Command,
};
use wasmi::{
    core::{Trap, ValueType},
    Config, Engine, FuncType, Linker, Module, Store, Value,
};

fn compile(source: &Path, bindings: &BTreeMap<String, Binding>) -> Result<Vec<u8>> {
    let tmp = tempfile::tempdir()?;
    let mut text =
        String::from("struct Address { handle: u32; }\nstruct SorobanI128 { handle: u32; }\n");
    let mut wrappers = String::new();
    let mut imports = Vec::new();
    for (name, b) in bindings {
        let raw = format!("bridge_{name}");
        let mut inputs = Vec::new();
        let mut public = Vec::new();
        let mut values = Vec::new();
        for (i, ty) in b.inputs.iter().enumerate() {
            inputs.push(format!("arg{i}: {}", ty.inf()));
            public.push(format!("arg{i}: {}", ty.object_name().unwrap_or(ty.inf())));
            values.push(if ty.object_name().is_some() {
                format!("arg{i}.handle")
            } else {
                format!("arg{i}")
            });
        }
        let ret = b
            .output
            .map_or(String::new(), |o| format!(" -> {}", o.inf()));
        writeln!(text, "external fn {raw}({}){ret};", inputs.join(", "))?;
        let result = b.output.map_or(String::new(), |o| {
            format!(" -> {}", o.object_name().unwrap_or(o.inf()))
        });
        let call = format!("{raw}({})", values.join(", "));
        let body = match b.output {
            None => call,
            Some(o) => match o.object_name() {
                Some(ty) => format!("return {ty} {{ handle: {call} }}"),
                None => format!("return {call}"),
            },
        };
        writeln!(
            wrappers,
            "fn {name}({}){result} {{ {body}; }}",
            public.join(", ")
        )?;
        imports.push(raw);
    }
    writeln!(text, "use {{ {} }} from host::soroban;", imports.join(", "))?;
    text.push_str(&wrappers);
    text.push_str(
        &fs::read_to_string(source).with_context(|| format!("reading {}", source.display()))?,
    );
    let input = tmp.path().join("scenario.inf");
    fs::write(&input, text)?;
    let compiler = env::var_os("INFC_PATH").unwrap_or_else(|| OsString::from("infc"));
    ensure!(
        Command::new(compiler)
            .arg(&input)
            .args(["--mode", "compile", "--out-dir"])
            .arg(tmp.path())
            .status()
            .context("start infc (set INFC_PATH or add infc to PATH)")?
            .success(),
        "compiling {}",
        source.display()
    );
    Ok(fs::read(tmp.path().join("scenario.wasm"))?)
}

fn run(file: &Path) -> Result<()> {
    let fixture: Fixture = serde_json::from_slice(&fs::read(file)?)?;
    ensure!(!fixture.runs.is_empty(), "fixture needs at least one run");
    let dir = file.parent().context("fixture directory")?;
    let host = Host::new(&fixture, dir)?;
    let bindings = Binding::all(&host, &fixture)?;
    let wasm = compile(&dir.join(&fixture.source), &bindings)?;
    let mut config = Config::default();
    config.consume_fuel(true);
    let engine = Engine::new(&config);
    let module = Module::new(&engine, wasm.as_slice())?;
    let mut linker = Linker::<Host>::new(&engine);
    for (name, b) in bindings {
        let ty = FuncType::new(
            b.inputs.iter().map(|t| t.wasm()),
            b.output.map(|o| o.wasm()),
        );
        linker.func_new(
            "soroban",
            &format!("bridge_{name}"),
            ty,
            move |mut c, args, results| {
                if let Some(v) = b
                    .call(c.data_mut(), args)
                    .map_err(|e| Trap::new(format!("{e:#}")))?
                {
                    results[0] = v;
                }
                Ok(())
            },
        )?;
    }
    let mut store = Store::new(&engine, host);
    store
        .add_fuel(10_000_000)
        .map_err(|e| anyhow::anyhow!("{e}"))?;
    let instance = linker.instantiate(&mut store, &module)?.start(&mut store)?;
    for case in fixture.runs {
        let fun = instance
            .get_func(&store, &case.entry)
            .with_context(|| format!("missing entry {}", case.entry))?;
        let ty = fun.ty(&store);
        ensure!(
            ty.results().is_empty() && ty.params().len() == case.args.len(),
            "scenario {} must return void and match its configured argument count",
            case.entry
        );
        let args = ty
            .params()
            .iter()
            .zip(&case.args)
            .map(|(ty, a)| {
                Ok(match ty {
                    ValueType::I64 => Value::I64(*a as i64),
                    ValueType::I32 => Value::I32(u32::try_from(*a)? as i32),
                    _ => bail!("non-integer scenario input"),
                })
            })
            .collect::<Result<Vec<_>>>()?;
        fun.call(&mut store, &args, &mut [])
            .with_context(|| format!("{}{:?}", case.entry, case.args))?;
        println!("PASS {}{:?}", case.entry, case.args);
    }
    Ok(())
}

fn main() -> Result<()> {
    let mut args = env::args_os().skip(1);
    let file = PathBuf::from(args.next().context("usage: infs-soroban FIXTURE.json")?);
    ensure!(args.next().is_none(), "usage: infs-soroban FIXTURE.json");
    run(&file)
}
