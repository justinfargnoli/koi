pub mod check {
    use crate::hir::ir::{Declaration, Inductive, Name, Term, HIR};

    pub mod GlobalEnvironment {

        use super::*;

        pub struct Context {
            declarations: Vec<Declaration>,
            // TODO: `universe_graph: uGraph.t`
        }

        impl Context {
            pub fn new() -> Context {
                Context {
                    declarations: Vec::new(),
                }
            }
        }

        enum Declaration {
            Constant(String, ConstantBody),
            Inductive(String, Inductive),
        }

        pub struct ConstantBody {
            typ: Term,
            body: Option<Term>,
            // TODO: `universes: universe_context`
        }
    }

    pub mod LocalEnvironment {
        use super::*;

        pub struct Context {
            pub declarations: Vec<Declaration>,
        }

        impl Context {
            pub fn new() -> Context {
                Context {
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

    pub fn type_check_hir(hir: &HIR) {
        let mut global = GlobalEnvironment::Context::new();
        let mut local = LocalEnvironment::Context::new();
        for declaration in hir.declarations.iter() {
            match declaration {
                Declaration::Constant(term) => {
                    type_check_term(&global, &mut local, term);
                    // TODO: add this to the global environment
                }
                Declaration::Inductive(inductive) => {
                    type_check_inductive(&global, &mut local, &inductive)
                    // TODO: add this to the global environment
                }
            }
        }
    }

    // assert when type checking fails
    // TODO: return error messages using ariadne.
    fn type_check_term(
        global: &GlobalEnvironment::Context,
        local: &mut LocalEnvironment::Context,
        term: &Term,
    ) -> Term {
        match term {
            Term::DeBruijnIndex(debruijn_index) => {
                // pass only if the `debruijn_index` is a local declaration
                local.declarations.get(*debruijn_index).unwrap().typ.clone()
            }
            Term::Sort(universe) => todo!(),
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

                local.push_declaration(name.clone(), None, from_type_type);
                let to_type_universe = match type_check_term(global, local, to_type) {
                    Term::Sort(ref universe) => universe,
                    _ => panic!(),
                };
                local.pop_declaration();

                Term::Sort(todo!()) // TODO: `Term::Sort(`Universe.sort_of_product s1 s2`)`
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
    fn type_check_inductive(
        global: &GlobalEnvironment::Context,
        local: &mut LocalEnvironment::Context,
        inductive: &Inductive,
    ) {
        todo!()
    }
}

mod pass {}
