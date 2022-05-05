use crate::{
    codegen,
    codegen::environment::global::Environment,
    hir::ir::{DeBruijnIndex, Term, Undefined},
};
use std::collections::HashSet;

fn free_variables_helper(
    global: &Environment,
    term: &Term,
    max_bound_debruijn_index: DeBruijnIndex,
    accumulator: &mut HashSet<DeBruijnIndex>,
) {
    match term {
        Term::DeBruijnIndex(debruijn_index) => {
            if (*debruijn_index) > max_bound_debruijn_index {
                accumulator.insert(debruijn_index - max_bound_debruijn_index - 1);
            }
        }
        Term::Lambda { body, .. } => {
            free_variables_helper(global, body, max_bound_debruijn_index + 1, accumulator);
        }
        Term::Match {
            inductive_name,
            scrutinee,
            branches,
            ..
        } => {
            let inductive = global.lookup_inductive(inductive_name);

            inductive
                .constructors
                .iter()
                .zip(branches.iter())
                .for_each(|(constructor, branch)| {
                    free_variables_helper(
                        global,
                        branch,
                        max_bound_debruijn_index
                            + codegen::Context::constructor_parameter_count(
                                &constructor.struct_type,
                            ),
                        accumulator,
                    )
                });

            free_variables_helper(global, scrutinee, max_bound_debruijn_index, accumulator);
        }
        Term::Constant(_) | Term::Constructor(_, _) => (),
        Term::Application { function, argument } => {
            free_variables_helper(global, &**function, max_bound_debruijn_index, accumulator);
            free_variables_helper(global, &**argument, max_bound_debruijn_index, accumulator);
        }
        Term::Fixpoint { .. } => todo!("Fixpoint"),
        Term::Undefined(undefined) => match undefined {
            Undefined::CodegenInnerConstructorFunction {
                constructor_parameter_count,
                ..
            } => (0..*constructor_parameter_count).for_each(|i| {
                free_variables_helper(
                    global,
                    &Term::DeBruijnIndex(i),
                    max_bound_debruijn_index,
                    accumulator,
                )
            }),
            _ => panic!("{:#?}", undefined),
        },
        _ => panic!("{:#?}", term),
    }
}

pub fn free_variables(
    global: &Environment,
    lambda: &Term,
    recursive_function: bool,
) -> HashSet<DeBruijnIndex> {
    match lambda {
        Term::Lambda { body, .. } => {
            let mut accumulator = HashSet::new();
            free_variables_helper(
                global,
                body,
                if recursive_function { 1 } else { 0 },
                &mut accumulator,
            );
            accumulator
        }
        _ => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        codegen::Context,
        hir::{examples, ir::Name},
    };
    use inkwell::context::Context as InkwellContext;

    fn test_free_variables_one_lambda(
        context: &Context,
        debruijn_index: DeBruijnIndex,
        expected_indexes: Vec<DeBruijnIndex>,
    ) {
        let unit_term = Term::Inductive("Unit".to_string());
        assert_eq!(
            free_variables(
                &context.global,
                &Term::Lambda {
                    name: Name::Anonymous,
                    parameter_name: Name::Anonymous,
                    parameter_type: Box::new(unit_term.clone()),
                    body: Box::new(Term::DeBruijnIndex(debruijn_index))
                },
                false
            ),
            HashSet::from_iter(expected_indexes)
        );
    }

    fn test_free_variables_two_lambdas(
        context: &Context,
        debruijn_index: DeBruijnIndex,
        expected_indexes: Vec<DeBruijnIndex>,
    ) {
        let unit_term = Term::Inductive("Unit".to_string());
        assert_eq!(
            free_variables(
                &context.global,
                &Term::Lambda {
                    name: Name::Anonymous,
                    parameter_name: Name::Anonymous,
                    parameter_type: Box::new(unit_term.clone()),
                    body: Box::new(Term::Lambda {
                        name: Name::Anonymous,
                        parameter_name: Name::Anonymous,
                        parameter_type: Box::new(unit_term),
                        body: Box::new(Term::Application {
                            function: Box::new(Term::DeBruijnIndex(debruijn_index)),
                            argument: Box::new(Term::DeBruijnIndex(debruijn_index))
                        }),
                    })
                },
                false
            ),
            HashSet::from_iter(expected_indexes)
        );
    }

    fn test_free_variables_one_recursive_lambda(
        context: &Context,
        debruijn_index: DeBruijnIndex,
        expected_indexes: Vec<DeBruijnIndex>,
    ) {
        let unit_term = Term::Inductive("Unit".to_string());
        assert_eq!(
            free_variables(
                &context.global,
                &Term::Lambda {
                    name: Name::Anonymous,
                    parameter_name: Name::Anonymous,
                    parameter_type: Box::new(unit_term.clone()),
                    body: Box::new(Term::DeBruijnIndex(debruijn_index))
                },
                true
            ),
            HashSet::from_iter(expected_indexes)
        );
    }

    #[test]
    fn test_free_variables() {
        let inkwell_context = InkwellContext::create();
        let mut context = Context::build(&inkwell_context);

        context.codegen_fresh_inductive(examples::unit());

        test_free_variables_one_lambda(&context, 0, vec![]);
        test_free_variables_one_lambda(&context, 1, vec![0]);
        test_free_variables_one_lambda(&context, 2, vec![1]);

        test_free_variables_two_lambdas(&context, 0, vec![]);
        test_free_variables_two_lambdas(&context, 1, vec![]);
        test_free_variables_two_lambdas(&context, 2, vec![0]);
        test_free_variables_two_lambdas(&context, 3, vec![1]);

        test_free_variables_one_recursive_lambda(&context, 0, vec![]);
        test_free_variables_one_recursive_lambda(&context, 1, vec![]);
        test_free_variables_one_recursive_lambda(&context, 2, vec![0]);
        test_free_variables_one_recursive_lambda(&context, 3, vec![1]);
    }

    #[test]
    fn list_append() {
        let inkwell_context = InkwellContext::create();
        let mut context = Context::build(&inkwell_context);

        context.codegen_fresh_inductive(examples::list());

        let list_append_lambda = match examples::list_append().get_constant(1) {
            Term::Fixpoint { body, .. } => body.clone(),
            _ => panic!(),
        };

        assert_eq!(
            free_variables(&context.global, &list_append_lambda, true),
            HashSet::new()
        );

        assert_eq!(
            free_variables(
                &context.global,
                &match *list_append_lambda {
                    Term::Lambda { body, .. } => {
                        *body
                    }
                    _ => panic!(),
                },
                false
            ),
            HashSet::from_iter(vec![1])
        );
    }

    #[test]
    fn nat_add() {
        let inkwell_context = InkwellContext::create();
        let mut context = Context::build(&inkwell_context);

        context.codegen_fresh_inductive(examples::nat());

        let nat_add_lambda = match examples::nat_add().get_constant(1) {
            Term::Fixpoint { body, .. } => body.clone(),
            _ => panic!(),
        };

        assert_eq!(
            free_variables(&context.global, &nat_add_lambda, true),
            HashSet::new()
        );

        assert_eq!(
            free_variables(
                &context.global,
                &match *nat_add_lambda {
                    Term::Lambda { body, .. } => {
                        *body
                    }
                    _ => panic!(),
                },
                false
            ),
            HashSet::from_iter(vec![0, 1])
        );
    }
}
