#![allow(unused_imports)]
use std::collections::HashMap;
use std::path::PathBuf;
mod parse;
use serde_lexpr::from_str;

#[derive(Debug)]
struct Crate {
    mods: HashMap<PathBuf, parse::Module>,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let meow = parse_crate("example.yafl")?;
    println!("{meow:?}");
    Ok(())
}

fn parse_crate(fp: &str) -> Result<Crate, Box<dyn std::error::Error>> {
    use std::fs::canonicalize as canon;
    use crate::parse::*;
    let mut mods = HashMap::new();
    let starting_fp = canon(fp)?;
    let cwd = starting_fp.parent().ok_or_else(|| "wrf".to_owned())?.to_owned();
    let mut files = vec![starting_fp];
    while let Some(file) = files.pop() {
        let source = std::fs::read_to_string(&file)?;
        let module: Module = serde_lexpr::from_str(&source)?;
        for decl in module.decls.iter().rev() {
            match decl {
                Decl::ExternMod(_name, path) => {
                    let new_path = canon(cwd.join(path))?;
                    if &new_path == &file || mods.contains_key(&new_path) || files.contains(&new_path) { continue; }
                    files.push(new_path);
                }
                _ => {}
            };
        }
        mods.insert(file, module);
    }
    Ok(Crate { mods })
}
