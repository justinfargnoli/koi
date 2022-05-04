use crate::hir::ir::Term;

fn dead_function_elimination(term: Term) -> Option<Term> {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unchanged(term: Term) {
        assert_eq!(dead_function_elimination(term.clone()).unwrap(), term);
    }

    #[test]
    #[ignore]
    fn non_lambda_unchanged() {
        unchanged(Term::DeBruijnIndex(0))
    }

    #[test]
    #[ignore]
    fn simple_lambda_removed() {
        // assert_eq!(dead_function_elimination(Term::Lambda {}))
    }
}
