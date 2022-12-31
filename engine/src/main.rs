use z3::ast::Ast;
use z3::*;

fn main() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let opt = Optimize::new(&ctx);

    opt.
}
