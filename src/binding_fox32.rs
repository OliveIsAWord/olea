use crate::compiler_prelude::*;
use crate::ir::*;
use std::fmt::Write;

pub fn gen_program(program: &Program) -> String {
    let Program {
        functions,
        function_tys,
        tys,
        ..
    } = program;
    let mut code_buffer = String::new();
    let code = &mut code_buffer;
    for (name, ty) in function_tys {
        if functions.contains_key(name) {
            continue;
        }
        let TyKind::Function {
            params, returns, ..
        } = &tys[*ty]
        else {
            unreachable!();
        };
        gen_function(code, name, params, returns);
    }
    code_buffer
}

fn gen_function(
    code: &mut String,
    name: &str,
    params: &IndexMap<Str, (IsAnon, Ty)>,
    returns: &[Ty],
) {
    writeln!(code, "{name}:").unwrap();
    let const_address_name = name.to_ascii_uppercase();
    if !params.is_empty() {
        writeln!(code, "    pop rfp").unwrap();
        for (i, param) in params.keys().enumerate() {
            writeln!(code, "    pop r{i} ; {param}").unwrap();
        }
        writeln!(code, "    push rfp").unwrap();
    }
    if returns.is_empty() {
        writeln!(code, "    jmp [{const_address_name}]").unwrap();
    } else {
        writeln!(code, "    call [{const_address_name}]").unwrap();
        writeln!(code, "    pop rfp").unwrap();
        for i in 0..returns.len() {
            writeln!(code, "    push r{i}").unwrap();
        }
        writeln!(code, "    jmp rfp").unwrap();
    }
}
