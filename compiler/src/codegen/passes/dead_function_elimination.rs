// use crate::hir::ir::Term;

// fn is_computationally_irrelevant(term_type: &Term) -> bool {
//     match term_type {
//         Term::Sort(_) => true,
//         Term::DeBruijnIndex(_) => todo!("{:#?}", term_type),
//         _ => false,
//     }
// }

// fn decrement_debruijn_indexes(term: &mut Term) {
//     match term {
//         Term::DeBruijnIndex(index) => *index -= 1,
//         Term::Lambda { .. } => (),
//         Term::Application { function, argument } => {
//             decrement_debruijn_indexes(&mut **function);
//             decrement_debruijn_indexes(&mut **argument);
//         }
//         Term::Match {
//             scrutinee,
//             branches,
//             ..
//         } => {
//             decrement_debruijn_indexes(&mut **scrutinee);

//             branches.iter_mut().for_each(|branch| {
//                 if todo!() {
//                     decrement_debruijn_indexes(branch);
//                 }
//             });
//         }
//         _ => ()
//     }
// }

// pub fn dead_function_elimination(term: Term) -> Term {
//     match term {
//         Term::Lambda {
//             name,
//             parameter_name,
//             parameter_type,
//             body,
//         } => {
//             if is_computationally_irrelevant(&*parameter_type) {
//                 decrement_debruijn_indexes(&mut *body);
//                 dead_function_elimination(*body)
//             } else {
//                 Term::Lambda {
//                     name,
//                     parameter_name,
//                     parameter_type,
//                     body: Box::new(dead_function_elimination(*body)),
//                 }
//             }
//         }
//         _ => todo!("{:#?}", term),
//     }
// }

// #[cfg(test)]
// mod tests {
//     use super::*;

//     fn unchanged(term: Term) {
//         assert_eq!(dead_function_elimination(term.clone()).unwrap(), term);
//     }

//     #[test]
//     #[ignore]
//     fn non_lambda_unchanged() {
//         unchanged(Term::DeBruijnIndex(0))
//     }

//     #[test]
//     #[ignore]
//     fn simple_lambda_removed() {
//         // assert_eq!(dead_function_elimination(Term::Lambda {}))
//     }
// }
