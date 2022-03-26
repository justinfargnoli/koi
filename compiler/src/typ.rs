pub mod check {
    use crate::hir::ir::{
        universe::{Expression, Level, Universe},
        Declaration, Inductive, Term, HIR,
    };
    use environment::{global, local};

    mod environment {
        pub mod global {
            use crate::hir::ir::{Inductive, Term};

            pub struct Environment {
                declarations: Vec<Declaration>,
                // TODO: `universe_graph: uGraph.t`
            }

            impl Environment {
                pub fn new() -> Environment {
                    Environment {
                        declarations: Vec::new(),
                    }
                }

                pub fn lookup_inductive(&self, name: &str) -> Inductive {
                    for declaration in &self.declarations {
                        if let Declaration::Inductive(inductive_name, inductive) = declaration {
                            if inductive_name == name {
                                return inductive.clone();
                            }
                        }
                    }
                    panic!()
                }

                pub fn push_inductive(&mut self, inductive: Inductive) {
                    self.declarations
                        .push(Declaration::Inductive(inductive.name.clone(), inductive))
                }
            }

            enum Declaration {
                Constant(String, ConstantBody),
                Inductive(String, Inductive),
            }

            struct ConstantBody {
                typ: Term,
                body: Option<Term>,
                // TODO: `universes: universe_context`
            }
        }

        pub mod local {
            use crate::hir::ir::{Name, Term};

            pub struct Environment {
                pub declarations: Vec<Declaration>,
            }

            impl Environment {
                pub fn new() -> Environment {
                    Environment {
                        declarations: Vec::new(),
                    }
                }

                pub fn push_declaration(&mut self, name: Name, typ: Term) {
                    self.declarations.push(Declaration {
                        name,
                        body: None,
                        typ,
                    })
                }

                pub fn pop_declaration(&mut self) {
                    self.declarations.pop();
                }
            }

            #[derive(Debug)]
            pub struct Declaration {
                name: Name,
                body: Option<Term>,
                pub typ: Term,
            }
        }
    }

    pub struct Context {
        global: global::Environment,
        local: local::Environment,
    }

    impl Context {
        pub fn new() -> Context {
            Context {
                global: global::Environment::new(),
                local: local::Environment::new(),
            }
        }

        pub fn type_check_hir(hir: &HIR) {
            let mut context = Context::new();
            for declaration in hir.declarations.iter() {
                match declaration {
                    Declaration::Constant(term) => {
                        context.type_check_term(term);
                        // TODO: add this to the global environment
                    }
                    Declaration::Inductive(inductive) => context.type_check_inductive(inductive),
                }
            }
        }

        pub fn type_check_fresh_term(term: &Term) -> Term {
            Context::new().type_check_term(term)
        }

        // assert when type checking fails
        // TODO: return error messages using ariadne.
        fn type_check_term(&mut self, term: &Term) -> Term {
            match term {
                Term::DeBruijnIndex(debruijn_index) => {
                    // pass only if the `debruijn_index` is a local declaration
                    self.local
                        .declarations
                        .get(*debruijn_index)
                        .unwrap()
                        .typ
                        .clone()
                }
                Term::Sort(universe) => {
                    assert_eq!(universe.length(), 1);
                    let universe_expression = universe.first();
                    assert_eq!(universe_expression.1, false);
                    match universe_expression.level() {
                        Level::Prop | Level::Set => {
                            Term::Sort(Universe::build_one(Expression::type_1()))
                        } // return Type 1
                        _ => Term::Sort(Universe::build_one(universe_expression.successor())),
                    }
                }
                Term::DependentProduct {
                    parameter_name,
                    parameter_type,
                    return_type,
                } => {
                    let parameter_type_type = self.type_check_term(parameter_type);
                    let parameter_type_universe = self.sort_of(&parameter_type);

                    self.local
                        .push_declaration(parameter_name.clone(), parameter_type_type.clone());

                    let return_type_type = self.type_check_term(return_type);
                    let return_type_universe = self.sort_of(&return_type);

                    self.local.pop_declaration();

                    Term::Sort(Universe::sort_of_product(
                        &parameter_type_universe,
                        &return_type_universe,
                    ))
                }
                Term::Lambda {
                    parameter_name,
                    parameter_type,
                    body,
                } => {
                    self.type_check_term(parameter_type);

                    self.local
                        .push_declaration(parameter_name.clone(), (**parameter_type).clone());
                    let body_type = self.type_check_term(body);
                    self.local.pop_declaration();

                    Term::DependentProduct {
                        parameter_name: parameter_name.clone(),
                        parameter_type: parameter_type.clone(),
                        return_type: Box::new(body_type),
                    }
                }
                Term::Inductive(identifier, _) => {
                    let _inductive = self.global.lookup_inductive(identifier);

                    // TODO: handle universes
                    term.clone()
                }
                Term::Fixpoint {
                    fixpoint_name,
                    fixpoint_type,
                    body,
                    ..
                } => {
                    self.type_check_term(fixpoint_type);

                    self.local
                        .push_declaration(fixpoint_name.clone(), (**fixpoint_type).clone());
                    assert_eq!(**fixpoint_type, self.type_check_term(body));
                    self.local.pop_declaration();

                    (**fixpoint_type).clone()
                }
                Term::Match {
                    inductive_name,
                    parameter_count,
                    type_info,
                    discriminee,
                    branches,
                } => todo!("Match"),
                Term::Application {
                    function,
                    arguments,
                } => {
                    let function_type = self.type_check_term(function);

                    if let Term::Application { .. } = **function {
                        panic!()
                    }

                    assert_ne!(arguments.len(), 0);

                    arguments.iter().for_each(|argument| todo!());

                    todo!()
                }
                _ => todo!("{:#?}", term),
            }
        }

        fn sort_of(&self, term: &Term) -> Universe {
            match term {
                Term::Sort(universe) => universe.clone(),
                Term::Inductive(name, _universe_instance) => {
                    // Q: does `universe_instance` have anything to do with this?
                    let inductive = self.global.lookup_inductive(name);
                    match inductive.arity {
                        Term::Sort(universe) => universe,
                        _ => panic!("{:#?}", inductive.arity),
                    }
                }
                Term::DependentProduct {
                    parameter_name,
                    parameter_type,
                    return_type,
                } => self
                    .sort_of(parameter_type)
                    .supremum(&self.sort_of(return_type)),
                _ => todo!("{:#?}", term),
            }
        }

        pub fn type_check_fresh_inductive(inductive: &Inductive) {
            Context::new().type_check_inductive(inductive);
        }

        fn well_formed_arity(arity: &Term) {
            match arity {
                Term::DependentProduct { return_type, .. } => {
                    Context::well_formed_arity(&*return_type)
                }
                Term::Sort(_) => (),
                _ => panic!("arity is not well formed"),
            }
        }

        // assert when type checking fails
        // TODO: return error messages using ariadne.
        fn type_check_inductive(&mut self, inductive: &Inductive) {
            Context::well_formed_arity(&inductive.arity);
            Context::type_check_fresh_term(&inductive.arity);

            self.global.push_inductive(inductive.clone());
            let mut constructor_universe_expressions = inductive
                .constructors
                .iter()
                .map(|constructor| self.sort_of(&constructor.typ))
                .map(|universe| universe.representative_expression().clone());
            if let Some(first_universe_expression) = constructor_universe_expressions.next() {
                constructor_universe_expressions.for_each(|universe_expression| {
                    assert_eq!(universe_expression, first_universe_expression)
                })
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::hir::{examples, ir::Name};

        #[test]
        fn identity_function() {
            let parameter_type = Box::new(Term::Sort(Universe::build_one(Expression::set())));
            assert_eq!(
                Context::type_check_fresh_term(&Term::Lambda {
                    parameter_name: Name::Named("a".to_string()),
                    parameter_type: parameter_type.clone(),
                    body: Box::new(Term::DeBruijnIndex(0)),
                }),
                Term::DependentProduct {
                    parameter_name: Name::Named("a".to_string()),
                    parameter_type: parameter_type.clone(),
                    return_type: parameter_type,
                }
            )
        }

        #[test]
        #[should_panic]
        fn identity_function_malformed() {
            Context::type_check_fresh_term(&Term::Lambda {
                parameter_name: Name::Named("a".to_string()),
                parameter_type: Box::new(Term::Sort(Universe::build_one(Expression::set()))),
                body: Box::new(Term::DeBruijnIndex(1)),
            });
        }

        #[test]
        fn unit() {
            Context::type_check_fresh_inductive(&examples::unit())
        }

        #[test]
        fn nat_type() {
            Context::type_check_fresh_inductive(&examples::nat())
        }

        #[test]
        fn nat_add() {
            Context::type_check_hir(&HIR {
                declarations: vec![
                    Declaration::Inductive(examples::nat()),
                    Declaration::Constant(examples::nat_add()),
                ],
            });
        }

        #[test]
        fn nat_identity() {
            Context::type_check_hir(&HIR {
                declarations: vec![
                    Declaration::Inductive(examples::nat()),
                    Declaration::Constant(examples::nat_identity()),
                ],
            });
        }

        #[test]
        fn nat_one() {
            Context::type_check_hir(&HIR {
                declarations: vec![
                    Declaration::Inductive(examples::nat()),
                    Declaration::Constant(examples::nat_one()),
                ],
            });
        }
    }
}
