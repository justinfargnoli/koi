use crate::{
    codegen::environment::global::Environment,
    hir::ir::{DeBruijnIndex, Term, Undefined},
};
use std::collections::HashSet;

fn free_variables_helper(
    global: &Environment,
    term: &Term,
    max_bound_debruijn_index: DeBruijnIndex,
) -> HashSet<DeBruijnIndex> {
    match term {
        Term::DeBruijnIndex(debruijn_index) => {
            if (*debruijn_index) > max_bound_debruijn_index {
                let mut set = HashSet::new();
                set.insert(debruijn_index - max_bound_debruijn_index - 1);
                set
            } else {
                HashSet::new()
            }
        }
        Term::Lambda { body, .. } => {
            free_variables_helper(global, body, max_bound_debruijn_index + 1)
        }
        Term::Match {
            inductive_name,
            branches,
            ..
        } => {
            let inductive = global.lookup_inductive(inductive_name);

            inductive
                .constructors
                .iter()
                .zip(branches.iter())
                .flat_map(|(constructor, branch)| {
                    free_variables_helper(
                        global,
                        branch,
                        max_bound_debruijn_index + constructor.struct_type.get_field_types().len(),
                    )
                })
                .collect()
        }
        Term::Constant(_) | Term::Constructor(_, _) => HashSet::new(),
        Term::Application { function, argument } => {
            let mut free_indexes =
                free_variables_helper(global, &**function, max_bound_debruijn_index);
            free_indexes.extend(
                &mut free_variables_helper(global, &**argument, max_bound_debruijn_index).iter(),
            );
            free_indexes
        }
        Term::Fixpoint { .. } => todo!("Fixpoint"),
        Term::Undefined(undefined) => match undefined {
            Undefined::CodegenInnerConstructorFunction {
                constructor_parameter_count,
                ..
            } => (0..*constructor_parameter_count)
                .map(|i| {
                    free_variables_helper(global, &Term::DeBruijnIndex(i), max_bound_debruijn_index)
                })
                .reduce(|mut a, b| {
                    a.extend(b);
                    a
                })
                .unwrap_or_default(),
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
            free_variables_helper(global, body, if recursive_function { 1 } else { 0 })
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
                    Term::Lambda { body, .. } => *body,
                    _ => panic!(),
                },
                false
            ),
            HashSet::from_iter(vec![1])
        );
    }
}
