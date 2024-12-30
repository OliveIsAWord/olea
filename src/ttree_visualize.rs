use crate::arborist::{Block, TokenTree as Tt};
use crate::compiler_types::Spanned;

pub fn visualize(block: &Block, src: &str) {
    visualize0(block, src, 0);
    eprintln!();
}

fn visualize0(block: &Block, src: &str, level: usize) {
    let indent = || {
        for _ in 0..level {
            eprint!("    ");
        }
    };
    for (i, item) in block.iter().enumerate() {
        if i != 0 {
            eprintln!();
        }
        indent();
        for Spanned { kind, span } in item {
            match kind {
                Tt::Plain(_) => eprint!("{:?} ", &src[span.clone()]),
                Tt::Paren(b, _) => {
                    eprintln!("(");
                    visualize0(b, src, level + 1);
                    eprintln!();
                    indent();
                    eprint!(") ");
                }
                Tt::Square(b, _) => {
                    eprintln!("[");
                    visualize0(b, src, level + 1);
                    eprintln!();
                    indent();
                    eprint!("] ");
                }
                Tt::IndentedBlock(b) => {
                    // eprintln!();
                    // indent();
                    eprintln!(":");
                    visualize0(b, src, level + 1);
                    indent();
                }
                Tt::ElseBlock(b) => {
                    eprintln!("else");
                    visualize0(b, src, level + 1);
                    indent();
                }
            }
        }
    }
}
