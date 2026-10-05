use crate::priv_prelude::*;

/*
pub fn parse(full_src: &Arc<str>) -> Result<ast::Program, ParseError> {
    let tokens = crate::token::tokenize(full_src)?;
    let program = crate::combinators::parse_to_completion(crate::parser::program(), &tokens.as_ref())?;
    Ok(program.unwrap())
}
*/

pub fn parse_prec_stmt(full_src: &Arc<str>) -> Result<ast::PrecStmt, ParseError> {
    let tokens = crate::token::tokenize(full_src)?;
    let expr_opt = crate::combinators::parse_to_completion(crate::parser::prec_stmt(), &tokens.as_ref())?;
    Ok(expr_opt.unwrap())
}

