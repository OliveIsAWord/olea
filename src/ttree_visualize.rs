use crate::arborist::{Block, TokenTree as Tt};
use crate::compiler_types::Spanned;

pub fn visualize(block: &Block, src: &str) {
    visualize0(block, src, 0);
    println!();
}

fn visualize0(block: &Block, src: &str, level: usize) {
    let indent = || {
        for _ in 0..level {
            print!("    ");
        }
    };
    for (i, item) in block.iter().enumerate() {
        if i != 0 {
            println!();
        }
        indent();
        for Spanned { kind, span } in item {
            match kind {
                Tt::Plain(_) => print!("{:?} ", &src[span.clone()]),
                Tt::Paren(b, _) => {
                    println!("(");
                    visualize0(b, src, level + 1);
                    println!();
                    indent();
                    print!(") ");
                }
                Tt::IndentedBlock(b) => {
                    // println!();
                    // indent();
                    println!(":");
                    visualize0(b, src, level + 1);
                    indent();
                }
                Tt::ElseBlock(b) => {
                    println!("else");
                    visualize0(b, src, level + 1);
                    indent();
                }
            }
        }
    }
}
