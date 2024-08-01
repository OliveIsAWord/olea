mod lexer;
mod parser;
use lexer::{tokenize, Span, Tokens};
use parser::{parse, Program};

fn main() {
    let src: String = std::fs::read_to_string("example.yafl").unwrap();
    let tokens: Tokens = tokenize(&src);
    for i in 0..tokens.kinds.len() {
        let Span { start, len } = tokens.spans[i];
        println!(
            "{:?}\t{}:{}\t{:?}",
            tokens.kinds[i],
            start,
            len,
            &src[start..start + len],
        );
    }
    let program: Program<Span> = parse(&tokens, &src);
    println!("{program:?}");
}
