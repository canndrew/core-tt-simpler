use {
    std::{
        env, fs,
        sync::Arc,
    },
    core_tt_simpler::{CheckCtx, Check},
};

fn main() {
    let err = match run() {
        Ok(()) => return,
        Err(err) => err,
    };
    eprintln!("{}", err);
}

fn run() -> Result<(), String> {
    let Some(path) = env::args_os().skip(1).next() else {
        return Err(format!("expected a filename"));
    };
    let src = match fs::read_to_string(&path) {
        Ok(src) => src,
        Err(err) => return Err(format!("error reading {}: {}", path.display(), err)),
    };
    let src = Arc::from(src);
    let prec_stmt = match parser::parse_prec_stmt(&src) {
        Ok(prec_stmt) => prec_stmt,
        Err(err) => return Err(format!("parse error: {}", err)),
    };
    let (ctx, checked) = CheckCtx::with_builtins(|ch| {
        prec_stmt.check(ch)
    });
    let (ty, tm) = match checked.solve(ctx) {
        Ok((ty, tm)) => (ty, tm),
        Err(err) => return Err(format!("typecheck error: {}", err)),
    };
    let ty = ty.deep_nf();
    let tm = tm.deep_nf();

    println!("{}", core_tt_simpler::pprint::pprint(ty));
    println!("{}", core_tt_simpler::pprint::pprint(tm));

    Ok(())
}
