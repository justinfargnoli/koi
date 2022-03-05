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

                pub fn push_declaration(&mut self, name: Name, body: Option<Term>, typ: Term) {
                    self.declarations.push(Declaration { name, body, typ })
                }

                pub fn pop_declaration(&mut self) {
                    self.declarations.pop();
                }
            }

            pub struct Declaration {
                name: Name,
                body: Option<Term>,
                pub typ: Term,
            }
        }
    }

    pub fn type_check_hir(hir: &HIR) {
        let global = global::Environment::new();
        let mut local = local::Environment::new();
        for declaration in hir.declarations.iter() {
            match declaration {
                Declaration::Constant(term) => {
                    type_check_term(&global, &mut local, term);
                    // TODO: add this to the global environment
                }
                Declaration::Inductive(inductive) => {
                    type_check_inductive(&global, &inductive)
                    // TODO: add this to the global environment
                }
            }
        }
    }

    // assert when type checking fails
    // TODO: return error messages using ariadne.
    fn type_check_term(
        global: &global::Environment,
        local: &mut local::Environment,
        term: &Term,
    ) -> Term {
        match term {
            Term::DeBruijnIndex(debruijn_index) => {
                // pass only if the `debruijn_index` is a local declaration
                local.declarations.get(*debruijn_index).unwrap().typ.clone()
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
                name,
                from_type,
                to_type,
            } => {
                let from_type_type = type_check_term(global, local, from_type);
                let from_type_universe = match from_type_type {
                    Term::Sort(ref universe) => universe,
                    _ => panic!(),
                };

                local.push_declaration(name.clone(), None, from_type_type.clone());
                let to_type_type = type_check_term(global, local, to_type);
                let to_type_universe = match to_type_type {
                    Term::Sort(ref universe) => universe,
                    _ => panic!(),
                };
                local.pop_declaration();

                Term::Sort(Universe::sort_of_product(
                    from_type_universe,
                    to_type_universe,
                ))
            }
            Term::Lambda { name, typ, body } => {
                type_check_term(global, local, typ);

                local.push_declaration(name.clone(), None, (**typ).clone());
                let body_type = type_check_term(global, local, body);
                local.pop_declaration();

                Term::DependentProduct {
                    name: name.clone(),
                    from_type: typ.clone(),
                    to_type: Box::new(body_type),
                }
            }
            _ => todo!(),
        }
    }

    // assert when type checking fails
    // TODO: return error messages using ariadne.
    fn type_check_inductive(global: &global::Environment, inductive: &Inductive) {
        todo!()
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::hir::ir::{universe::Level, Name};

        #[test]
        fn identity_function() {
            let mut hir = HIR::new();
            hir.declarations.push(Declaration::Constant(Term::Lambda {
                name: Name::Named("identity_function".to_string()),
                typ: Box::new(Term::DependentProduct {
                    name: Name::Named("a".to_string()),
                    from_type: Box::new(Term::Sort(Universe::build_one(Expression::build(
                        Level::Set,
                        false,
                    )))),
                    to_type: Box::new(Term::Sort(Universe::build_one(Expression::build(
                        Level::Set,
                        false,
                    )))),
                }),
                body: Box::new(Term::DeBruijnIndex(0)),
            }));
            type_check_hir(&hir);
        }
    }
}

mod pass {}
