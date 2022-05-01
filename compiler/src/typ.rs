pub mod check {
    use crate::{
        hir,
        hir::ir::{Declaration, Inductive, Name, Sort, Term, HIR},
    };
    use environment::{global, local};

    mod environment {
        pub mod global {
            use crate::hir::ir::{Inductive, Term};

            enum Declaration {
                Inductive(Inductive),
                Constant { name: String, typ: Term },
            }

            #[derive(Default)]
            pub struct Environment {
                declarations: Vec<Declaration>,
            }

            impl Environment {
                pub fn lookup_inductive(&self, name: &str) -> Inductive {
                    for declaration in &self.declarations {
                        if let Declaration::Inductive(inductive) = declaration {
                            if inductive.name == name {
                                return inductive.clone();
                            }
                        }
                    }
                    panic!()
                }

                fn name_is_unique(&self, name: &str) {
                    for declaration in &self.declarations {
                        match declaration {
                            Declaration::Inductive(inductive) => assert_ne!(inductive.name, name),
                            Declaration::Constant{ name: constant_name, .. } => assert_ne!(constant_name, name),
                        }
                    }
                }

                pub fn push_inductive(&mut self, inductive: Inductive) {
                    self.name_is_unique(&inductive.name);
                    self.declarations.push(Declaration::Inductive(inductive))
                }

                pub fn push_constant(&mut self, name: String, typ: Term) {
                    self.name_is_unique(&name);
                    self.declarations.push(Declaration::Constant { name, typ })
                }

                pub fn lookup_constant_type(&self, name: &str) -> Term {
                    for declaration in &self.declarations {
                        if let Declaration::Constant {
                            name: constant_name,
                            typ,
                        } = declaration
                        {
                            if constant_name == name {
                                return typ.clone();
                            }
                        }
                    }
                    panic!()
                }
            }
        }

        pub mod local {
            use crate::hir::ir::Term;

            #[derive(Default)]
            pub struct Environment {
                pub declarations: Vec<Declaration>,
            }

            impl Environment {
                pub fn push_declaration(&mut self, /* name: Name, */ typ: Term) {
                    self.declarations.push(Declaration {
                        // name,
                        // body: None,
                        typ,
                    })
                }

                pub fn pop_declaration(&mut self) {
                    self.declarations.pop();
                }

                pub fn is_empty(&self) -> bool {
                    self.declarations.is_empty()
                }
            }

            #[derive(Debug, Clone)]
            pub struct Declaration {
                // name: Name,
                // body: Option<Term>,
                pub typ: Term,
            }
        }
    }

    #[derive(Default)]
    pub struct Context {
        global: global::Environment,
        local: local::Environment,
    }

    impl Context {
        pub fn type_check_hir(hir: &HIR) {
            let mut context = Context::default();
            for declaration in hir.declarations.iter() {
                assert!(context.local.is_empty());

                match declaration {
                    Declaration::Constant(term) => {
                        let term_type = context.type_check_term(term);

                        // Add term to global environment if it has a name.
                        match term {
                            Term::Lambda {
                                name: Name::Named(name),
                                ..
                            } => context.global.push_constant(name.clone(), term_type),
                            Term::Fixpoint {
                                expression_type,
                                body,
                                ..
                            } => match &**body {
                                Term::Lambda {
                                    name: Name::Named(name),
                                    ..
                                } => context
                                    .global
                                    .push_constant(name.clone(), (**expression_type).clone()),
                                _ => unreachable!(),
                            },
                            _ => (),
                        }
                    }
                    Declaration::Inductive(inductive) => context.type_check_inductive(inductive),
                }

                assert!(context.local.is_empty());
            }
        }

        pub fn type_check_fresh_term(term: &Term) -> Term {
            Context::default().type_check_term(term)
        }

        fn type_check_term(&mut self, term: &Term) -> Term {
            match term {
                Term::DeBruijnIndex(debruijn_index) => {
                    // pass only if the `debruijn_index` is a local declaration
                    hir::ir::debruijn_index_lookup(&self.local.declarations, *debruijn_index)
                        .typ
                        .clone()
                }
                Term::Sort(sort) => match sort {
                    Sort::Prop | Sort::Set => Term::Sort(Sort::Type(1)),
                    Sort::Type(number) => Term::Sort(Sort::Type(number + 1)),
                },
                Term::DependentProduct {
                    // parameter_name,
                    parameter_type,
                    return_type,
                    ..
                } => {
                    let parameter_type_sort = match self.type_check_term(parameter_type) {
                        Term::Sort(sort) => sort,
                        _ => unreachable!(),
                    };

                    self.local.push_declaration(
                        /* parameter_name.clone(), */ (**parameter_type).clone(),
                    );

                    let return_type_sort = match self.type_check_term(return_type) {
                        Term::Sort(sort) => sort,
                        _ => unreachable!(),
                    };

                    self.local.pop_declaration();

                    Term::Sort(match (parameter_type_sort, return_type_sort) {
                        (_, Sort::Prop) => Sort::Prop,
                        (Sort::Set, Sort::Set) | (Sort::Prop, Sort::Set) => Sort::Set,
                        (Sort::Type(parameter_number), Sort::Type(return_number)) => {
                            Sort::Type(std::cmp::max(parameter_number, return_number))
                        }
                        (_, Sort::Type(number)) | (Sort::Type(number), _) => Sort::Type(number),
                    })
                }
                Term::Lambda {
                    parameter_name,
                    parameter_type,
                    body,
                    ..
                } => {
                    self.type_check_term(parameter_type);

                    self.local.push_declaration(
                        /* parameter_name.clone(), */ (**parameter_type).clone(),
                    );
                    let body_type = self.type_check_term(body);
                    self.local.pop_declaration();

                    Term::DependentProduct {
                        parameter_name: parameter_name.clone(),
                        parameter_type: parameter_type.clone(),
                        return_type: Box::new(body_type),
                    }
                }
                Term::Application { function, argument } => {
                    let function_type = self.type_check_term(function);
                    let argument_type = self.type_check_term(argument);

                    // This should be a cumulativity relation, not a direct match. (i.e. it should be <= not ==)
                    match function_type {
                        Term::DependentProduct {
                            parameter_type,
                            return_type,
                            ..
                        } => {
                            assert_eq!(argument_type, *parameter_type);
                            (*return_type).clone()
                        }
                        _ => {
                            // dbg!(self.local.declarations.clone());
                            // todo!("{:#?}, {:#?}", function_type, function)
                            todo!("{:#?}", function_type)
                        }
                    }
                }
                Term::Constant(name) => self.global.lookup_constant_type(name),
                Term::Inductive(name) => {
                    let inductive = self.global.lookup_inductive(name);
                    inductive.typ
                }
                Term::Constructor(inductive_name, branches_index) => {
                    let inductive = self.global.lookup_inductive(inductive_name);

                    let constructor = inductive.constructors.get(*branches_index).unwrap();

                    constructor.typ.clone()
                }
                Term::Match {
                    inductive_name,
                    scrutinee,
                    return_type,
                    branches,
                    ..
                } => {
                    let inductive = self.global.lookup_inductive(inductive_name.as_str());

                    assert_eq!(
                        self.type_check_term(scrutinee),
                        Term::Inductive((*inductive_name).clone())
                    );

                    self.type_check_term(return_type);

                    branches
                        .iter()
                        .zip(
                            inductive
                                .constructors
                                .iter()
                                .map(|constructor| &constructor.typ),
                        )
                        .for_each(|(branch, constructor_type)| {
                            fn add_constructor_fields_to_environment(
                                local_environment: &mut environment::local::Environment,
                                constructor_type: &Term,
                            ) -> usize {
                                match constructor_type {
                                    Term::DependentProduct {
                                        // parameter_name,
                                        parameter_type,
                                        return_type,
                                        ..
                                    } => {
                                        local_environment.push_declaration(
                                            // parameter_name.clone(),
                                            (**parameter_type).clone(),
                                        );
                                        let number_of_declarations_added =
                                            add_constructor_fields_to_environment(
                                                local_environment,
                                                &(**return_type),
                                            );
                                        number_of_declarations_added + 1
                                    }
                                    Term::Inductive(_) => 0,
                                    _ => unreachable!("{:#?}", constructor_type),
                                }
                            }

                            let number_of_declarations_added =
                                add_constructor_fields_to_environment(
                                    &mut self.local,
                                    constructor_type,
                                );

                            assert_eq!(**return_type, self.type_check_term(branch));

                            for _ in 0..number_of_declarations_added {
                                self.local.pop_declaration();
                            }
                        });

                    (**return_type).clone()
                }
                Term::Fixpoint {
                    expression_type,
                    body,
                    ..
                } => {
                    self.type_check_term(expression_type);

                    self.local.push_declaration((**expression_type).clone());
                    assert_eq!(**expression_type, self.type_check_term(body));
                    self.local.pop_declaration();

                    (**expression_type).clone()
                }
            }
        }

        pub fn type_check_fresh_inductive(inductive: &Inductive) {
            Context::default().type_check_inductive(inductive);
        }

        fn check_inductive_type_form(inductive_type: &Term, parameter_count: usize) {
            match inductive_type {
                Term::DependentProduct { return_type, .. } => Context::check_inductive_type_form(
                    return_type,
                    if parameter_count == 0 {
                        0
                    } else {
                        parameter_count - 1
                    },
                ),
                Term::Sort(_) => (),
                _ => unreachable!("{:#?}", inductive_type),
            }
        }

        fn check_constructor_type_form(
            inductive_name: &str,
            constructor_type: &Term,
            parameter_count: usize,
        ) {
            match constructor_type {
                Term::DependentProduct { return_type, .. } => {
                    Context::check_constructor_type_form(
                        inductive_name,
                        return_type,
                        if parameter_count == 0 {
                            0
                        } else {
                            parameter_count - 1
                        },
                    )
                }
                Term::Inductive(name) => assert_eq!(inductive_name, name),
                _ => unreachable!(),
            }
        }

        fn type_check_inductive(&mut self, inductive: &Inductive) {
            Context::type_check_fresh_term(&inductive.typ);

            Context::check_inductive_type_form(&inductive.typ, inductive.parameter_count);

            self.global.push_inductive(inductive.clone());

            inductive.constructors.iter().for_each(|constructor| {
                let constructor_type_type = self.type_check_term(&constructor.typ);

                assert!(Term::is_sort(&constructor_type_type));

                Context::check_constructor_type_form(
                    &inductive.name,
                    &constructor.typ,
                    inductive.parameter_count,
                );
            });
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::hir::{examples, ir::Name};

        #[test]
        fn identity_function() {
            let parameter_type = Box::new(Term::Sort(Sort::Set));
            assert_eq!(
                Context::type_check_fresh_term(&Term::Lambda {
                    name: Name::Anonymous,
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
                name: Name::Anonymous,
                parameter_name: Name::Named("a".to_string()),
                parameter_type: Box::new(Term::Sort(Sort::Set)),
                body: Box::new(Term::DeBruijnIndex(1)),
            });
        }

        #[test]
        fn unit() {
            Context::type_check_fresh_inductive(&examples::unit())
        }

        #[test]
        #[should_panic]
        fn generic_unit() {
            Context::type_check_fresh_inductive(&examples::generic_unit())
        }

        #[test]
        fn single_argument_constructor2() {
            Context::type_check_fresh_inductive(&examples::single_argument_constructor2())
        }

        #[test]
        fn single_argument_constructor() {
            Context::type_check_hir(&examples::single_argument_constructor())
        }

        #[test]
        fn nat_type() {
            Context::type_check_fresh_inductive(&examples::nat())
        }

        #[test]
        fn nat_add() {
            Context::type_check_hir(&examples::nat_add());
        }

        #[test]
        fn nat_identity() {
            Context::type_check_hir(&examples::nat_identity());
        }

        #[test]
        fn global_constant_use_nat_identity() {
            Context::type_check_hir(&examples::global_constant_use_nat_identity());
        }

        #[test]
        fn nat_zero() {
            Context::type_check_hir(&examples::nat_zero());
        }

        #[test]
        fn nat_one() {
            Context::type_check_hir(&examples::nat_one());
        }

        #[test]
        fn nat_left() {
            Context::type_check_hir(&examples::nat_left());
        }

        #[test]
        fn nat_to_zero() {
            Context::type_check_hir(&examples::nat_to_zero());
        }

        #[test]
        #[ignore]
        fn list_type() {
            Context::type_check_fresh_inductive(&examples::list())
        }

        #[test]
        #[ignore]
        fn list_append() {
            Context::type_check_hir(&examples::list_append());
        }

        #[test]
        #[ignore]
        fn vector_type() {
            Context::type_check_hir(&examples::vector())
        }

        #[test]
        #[ignore]
        fn vector_append() {
            Context::type_check_hir(&examples::vector_append());
        }

        #[test]
        #[should_panic]
        fn same_name_types_inductive() {
            Context::type_check_hir(&HIR {
                declarations: vec![
                    Declaration::Inductive(examples::unit()),
                    Declaration::Inductive(examples::unit()),
                ],
            });
        }

        #[test]
        #[should_panic]
        fn same_name_types_constant() {
            Context::type_check_hir(&HIR {
                declarations: vec![
                    Declaration::Inductive(examples::nat()),
                    Declaration::Constant(examples::nat_add().get_constant(1).clone()),
                    Declaration::Constant(examples::nat_add().get_constant(1).clone()),
                ],
            });
        }
    }
}
