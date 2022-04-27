pub mod ir {
    #[derive(Default)]
    pub struct HIR {
        pub declarations: Vec<Declaration>,
    }

    #[derive(Debug, Clone)]
    pub enum Declaration {
        Constant(Term),
        Inductive(Inductive),
    }

    pub type Identifier = String;

    #[derive(Clone, Debug)]
    pub struct Inductive {
        pub name: Identifier,
        pub parameter_count: usize,
        pub typ: Term,
        pub constructors: Vec<Constructor>,
    }

    #[derive(Clone, Debug)]
    pub struct Constructor {
        pub name: Identifier,
        pub typ: Term,
    }

    pub type DeBruijnIndex = usize;
    type BranchesCount = usize;

    #[derive(Clone, Debug, PartialEq)]
    pub enum Term {
        DeBruijnIndex(DeBruijnIndex),
        Sort(Sort),
        DependentProduct {
            parameter_name: Name,
            parameter_type: Box<Term>,
            return_type: Box<Term>,
        },
        Lambda {
            name: Name,
            parameter_name: Name,
            parameter_type: Box<Term>,
            body: Box<Term>,
        },
        Application {
            function: Box<Term>,
            argument: Box<Term>,
        },
        Constant(String),
        Inductive(String),
        Constructor(String, BranchesCount),
        Match {
            inductive_name: String,
            return_type: Box<Term>,
            scrutinee: Box<Term>,
            branches: Vec<Term>,
        },
        Fixpoint {
            name: String,
            expression_type: Box<Term>,
            body: Box<Term>,
        },
    }

    impl Term {
        pub fn is_sort(term: &Term) -> bool {
            matches!(term, Term::Sort(_))
        }
    }

    #[derive(Clone, Debug, PartialEq)]
    pub enum Name {
        Anonymous,
        Named(Identifier),
    }

    #[derive(Clone, Debug, PartialEq)]
    pub enum Sort {
        Prop,
        Set,
        Type(u32),
    }
}

pub mod examples {
    use super::ir::*;

    /// enum Unit() : Type 0 {}
    pub fn unit() -> Inductive {
        Inductive {
            name: "Unit".to_string(),
            parameter_count: 0,
            typ: Term::Sort(Sort::Set),
            constructors: Vec::new(),
        }
    }

    /// enum Nat() : Type 0 {
    ///     O() -> Nat,
    ///     S(_ : Nat) -> Nat,
    /// }
    pub fn nat() -> Inductive {
        let natural = "Nat".to_string();
        let zero = "O".to_string();
        let successor = "S".to_string();

        Inductive {
            name: natural.clone(),
            parameter_count: 0,
            typ: Term::Sort(Sort::Set),
            constructors: vec![
                Constructor {
                    name: zero,
                    typ: Term::Inductive(natural.clone()),
                },
                Constructor {
                    name: successor,
                    typ: Term::DependentProduct {
                        parameter_name: Name::Anonymous,
                        parameter_type: Box::new(Term::Inductive(natural.clone())),
                        return_type: Box::new(Term::Inductive(natural)),
                    },
                },
            ],
        }
    }

    /// func rec add(a b : Nat) -> Nat {
    ///     match a -> Nat {
    ///       Nat.O => b
    ///       Nat.S(x : Nat) => Nat.S(add(x, b))
    ///     }
    /// }
    pub fn nat_add() -> HIR {
        let nat = nat();

        let add_str = "add".to_string();
        let nat_term = Box::new(Term::Inductive(nat.name.clone()));
        let a = Name::Named("a".to_string());
        let b = Name::Named("b".to_string());

        let add = Term::Fixpoint {
            name: "add".to_string(),
            expression_type: Box::new(Term::DependentProduct {
                parameter_name: a.clone(),
                parameter_type: nat_term.clone(),
                return_type: Box::new(Term::DependentProduct {
                    parameter_name: b.clone(),
                    parameter_type: nat_term.clone(),
                    return_type: nat_term.clone(),
                }),
            }),
            body: Box::new(Term::Lambda {
                name: Name::Named(add_str),
                parameter_name: a,
                parameter_type: nat_term.clone(),
                body: Box::new(Term::Lambda {
                    name: Name::Anonymous,
                    parameter_name: b,
                    parameter_type: nat_term.clone(),
                    body: Box::new(Term::Match {
                        inductive_name: nat.name.clone(),
                        return_type: nat_term,
                        scrutinee: Box::new(Term::DeBruijnIndex(1)),
                        branches: vec![
                            Term::DeBruijnIndex(0),
                            Term::Application {
                                function: Box::new(Term::Constructor(nat.name.clone(), 1)),
                                argument: Box::new(Term::Application {
                                    function: Box::new(Term::Application {
                                        function: Box::new(Term::DeBruijnIndex(3)),
                                        argument: Box::new(Term::DeBruijnIndex(0)),
                                    }),
                                    argument: Box::new(Term::DeBruijnIndex(1)),
                                }),
                            },
                        ],
                    }),
                }),
            }),
        };

        HIR {
            declarations: vec![Declaration::Inductive(nat), Declaration::Constant(add)],
        }
    }

    /// func identity(a : Nat) -> Nat {
    ///     a
    /// }
    pub fn nat_identity() -> HIR {
        let nat = nat();

        let identity = Term::Lambda {
            name: Name::Named("identity".to_string()),
            parameter_name: Name::Named("x".to_string()),
            parameter_type: Box::new(Term::Inductive(nat.name.clone())),
            body: Box::new(Term::DeBruijnIndex(0)),
        };

        HIR {
            declarations: vec![Declaration::Inductive(nat), Declaration::Constant(identity)],
        }
    }

    pub fn global_constant_use_nat_identity() -> HIR {
        let mut nat_identity_hir = nat_identity();

        nat_identity_hir
            .declarations
            .push(Declaration::Constant(Term::Lambda {
                name: Name::Anonymous,
                parameter_name: Name::Named("a".to_string()),
                parameter_type: Box::new(Term::Inductive("Nat".to_string())),
                body: Box::new(Term::Application {
                    function: Box::new(Term::Constant("identity".to_string())),
                    argument: Box::new(Term::DeBruijnIndex(0)),
                }),
            }));

        nat_identity_hir
    }

    /// func (_ : Nat) {
    ///     Nat.S(Nat.O)
    /// }
    pub fn nat_zero() -> HIR {
        let nat = nat();

        let nat_term = Box::new(Term::Inductive(nat.name.clone()));

        let zero = Term::Lambda {
            name: Name::Anonymous,
            parameter_name: Name::Anonymous,
            parameter_type: nat_term,
            body: Box::new(Term::Constructor(nat.name.clone(), 0)),
        };

        HIR {
            declarations: vec![Declaration::Inductive(nat), Declaration::Constant(zero)],
        }
    }

    /// func (_ : Nat) {
    ///     Nat.S(Nat.O)
    /// }
    pub fn nat_one() -> HIR {
        let nat = nat();

        let nat_term = Box::new(Term::Inductive(nat.name.clone()));

        let one = Term::Lambda {
            name: Name::Anonymous,
            parameter_name: Name::Anonymous,
            parameter_type: nat_term,
            body: Box::new(Term::Application {
                function: Box::new(Term::Constructor(nat.name.clone(), 1)),
                argument: Box::new(Term::Constructor(nat.name.clone(), 0)),
            }),
        };

        HIR {
            declarations: vec![Declaration::Inductive(nat), Declaration::Constant(one)],
        }
    }

    ///  enum List(T : Set) : Set {
    ///     Nil() -> List T,
    ///     Cons(head : T, tail : List T) -> List T,
    /// }
    pub fn list() -> Inductive {
        let list_name = "List".to_string();
        let t_name = "T".to_string();

        Inductive {
            name: list_name.clone(),
            parameter_count: 1,
            typ: Term::DependentProduct {
                parameter_name: Name::Named(t_name.clone()),
                parameter_type: Box::new(Term::Sort(Sort::Set)),
                return_type: Box::new(Term::Sort(Sort::Set)),
            },
            constructors: vec![
                Constructor {
                    name: "Nil".to_string(),
                    typ: Term::DependentProduct {
                        parameter_name: Name::Named(t_name.clone()),
                        parameter_type: Box::new(Term::Sort(Sort::Set)),
                        return_type: Box::new(Term::Application {
                            function: Box::new(Term::Inductive(list_name.clone())),
                            argument: Box::new(Term::DeBruijnIndex(0)),
                        }),
                    },
                },
                Constructor {
                    name: "Cons".to_string(),
                    typ: Term::DependentProduct {
                        parameter_name: Name::Named(t_name),
                        parameter_type: Box::new(Term::Sort(Sort::Set)),
                        return_type: Box::new(Term::DependentProduct {
                            parameter_name: Name::Named("head".to_string()),
                            parameter_type: Box::new(Term::DeBruijnIndex(0)),
                            return_type: Box::new(Term::DependentProduct {
                                parameter_name: Name::Named("tail".to_string()),
                                parameter_type: Box::new(Term::Application {
                                    function: Box::new(Term::Inductive(list_name.clone())),
                                    argument: Box::new(Term::DeBruijnIndex(1)),
                                }),
                                return_type: Box::new(Term::Application {
                                    function: Box::new(Term::Inductive(list_name)),
                                    argument: Box::new(Term::DeBruijnIndex(2)),
                                }),
                            }),
                        }),
                    },
                },
            ],
        }
    }

    /// func list_append(T : Set, a b : List T) -> List T {
    ///     match a -> List T {
    ///         List.Nil(T : Set) => b
    ///         List.Cons(T : Set, head : T, tail : List T) =>
    ///             List.Cons(T, head, list_append(T, tail, b))
    ///     }
    /// }
    pub fn list_append() -> HIR {
        let list_name = "List".to_string();
        let list_term = Term::Inductive(list_name.clone());
        let t_name = "T".to_string();
        let a_name = "a".to_string();

        let append = Term::Fixpoint {
            name: "list_append".to_string(),
            expression_type: Box::new(Term::DependentProduct {
                parameter_name: Name::Named(t_name.clone()),
                parameter_type: Box::new(Term::Sort(Sort::Set)),
                return_type: Box::new(Term::DependentProduct {
                    parameter_name: Name::Named(a_name.clone()),
                    parameter_type: Box::new(Term::Application {
                        function: Box::new(list_term.clone()),
                        argument: Box::new(Term::DeBruijnIndex(0)),
                    }),
                    return_type: Box::new(Term::DependentProduct {
                        parameter_name: Name::Named("b".to_string()),
                        parameter_type: Box::new(Term::Application {
                            function: Box::new(list_term.clone()),
                            argument: Box::new(Term::DeBruijnIndex(1)),
                        }),
                        return_type: Box::new(Term::Application {
                            function: Box::new(list_term.clone()),
                            argument: Box::new(Term::DeBruijnIndex(2)),
                        }),
                    }),
                }),
            }),
            body: Box::new(Term::Lambda {
                name: Name::Anonymous,
                parameter_name: Name::Named(t_name),
                parameter_type: Box::new(Term::Sort(Sort::Set)),
                body: Box::new(Term::Lambda {
                    name: Name::Anonymous,
                    parameter_name: Name::Named(a_name.clone()),
                    parameter_type: Box::new(Term::Application {
                        function: Box::new(list_term.clone()),
                        argument: Box::new(Term::DeBruijnIndex(0)),
                    }),
                    body: Box::new(Term::Lambda {
                        name: Name::Anonymous,
                        parameter_name: Name::Named(a_name),
                        parameter_type: Box::new(Term::Application {
                            function: Box::new(list_term.clone()),
                            argument: Box::new(Term::DeBruijnIndex(0)),
                        }),
                        body: Box::new(Term::Match {
                            inductive_name: list_name.clone(),
                            return_type: Box::new(Term::Application {
                                function: Box::new(list_term),
                                argument: Box::new(Term::DeBruijnIndex(2)),
                            }),
                            scrutinee: Box::new(Term::DeBruijnIndex(1)),
                            branches: vec![
                                Term::DeBruijnIndex(1),
                                Term::Application {
                                    function: Box::new(Term::Application {
                                        function: Box::new(Term::Application {
                                            function: Box::new(Term::Constructor(list_name, 1)),
                                            argument: Box::new(Term::DeBruijnIndex(2)),
                                        }),
                                        argument: Box::new(Term::DeBruijnIndex(1)),
                                    }),
                                    argument: Box::new(Term::Application {
                                        function: Box::new(Term::Application {
                                            function: Box::new(Term::Application {
                                                function: Box::new(Term::DeBruijnIndex(6)),
                                                argument: Box::new(Term::DeBruijnIndex(2)),
                                            }),
                                            argument: Box::new(Term::DeBruijnIndex(0)),
                                        }),
                                        argument: Box::new(Term::DeBruijnIndex(3)),
                                    }),
                                },
                            ],
                        }),
                    }),
                }),
            }),
        };

        let list = list();

        HIR {
            declarations: vec![Declaration::Inductive(list), Declaration::Constant(append)],
        }
    }

    ///  enum Vector(T : Set) : Nat -> Set {
    ///     Nil() -> Vector T Zero,
    ///     Cons(head : T, tail_length : Nat, tail : Vector T tail_length) -> Vector T (Successor tail_length),
    /// }
    pub fn vector() -> HIR {
        let vector_name = "Vector".to_string();
        let natural_name = "Nat".to_string();
        let tail_length_name = "tail_length".to_string();
        let t_name = "T".to_string();

        let vector = Inductive {
            name: vector_name.clone(),
            parameter_count: 1,
            typ: Term::DependentProduct {
                parameter_name: Name::Named(t_name.clone()),
                parameter_type: Box::new(Term::Sort(Sort::Set)),
                return_type: Box::new(Term::DependentProduct {
                    parameter_name: Name::Anonymous,
                    parameter_type: Box::new(Term::Inductive(natural_name.clone())),
                    return_type: Box::new(Term::Sort(Sort::Set)),
                }),
            },
            constructors: vec![
                Constructor {
                    name: "Nil".to_string(),
                    typ: Term::DependentProduct {
                        parameter_name: Name::Named(t_name.clone()),
                        parameter_type: Box::new(Term::Sort(Sort::Set)),
                        return_type: Box::new(Term::Application {
                            function: Box::new(Term::Application {
                                function: Box::new(Term::Inductive(vector_name.clone())),
                                argument: Box::new(Term::DeBruijnIndex(0)),
                            }),
                            argument: Box::new(Term::Constructor(natural_name.clone(), 0)),
                        }),
                    },
                },
                Constructor {
                    name: "Cons".to_string(),
                    typ: Term::DependentProduct {
                        parameter_name: Name::Named(t_name),
                        parameter_type: Box::new(Term::Sort(Sort::Set)),
                        return_type: Box::new(Term::DependentProduct {
                            parameter_name: Name::Named("head".to_string()),
                            parameter_type: Box::new(Term::DeBruijnIndex(0)),
                            return_type: Box::new(Term::DependentProduct {
                                parameter_name: Name::Named(tail_length_name),
                                parameter_type: Box::new(Term::Inductive(natural_name.clone())),
                                return_type: Box::new(Term::DependentProduct {
                                    parameter_name: Name::Named("tail".to_string()),
                                    parameter_type: Box::new(Term::Application {
                                        function: Box::new(Term::Application {
                                            function: Box::new(Term::Inductive(
                                                vector_name.clone(),
                                            )),
                                            argument: Box::new(Term::DeBruijnIndex(2)),
                                        }),
                                        argument: Box::new(Term::DeBruijnIndex(0)),
                                    }),
                                    return_type: Box::new(Term::Application {
                                        function: Box::new(Term::Application {
                                            function: Box::new(Term::Inductive(vector_name)),
                                            argument: Box::new(Term::DeBruijnIndex(3)),
                                        }),
                                        argument: Box::new(Term::Application {
                                            function: Box::new(Term::Constructor(natural_name, 1)),
                                            argument: Box::new(Term::DeBruijnIndex(1)),
                                        }),
                                    }),
                                }),
                            }),
                        }),
                    },
                },
            ],
        };

        let nat_inductive = nat();

        HIR {
            declarations: vec![
                Declaration::Inductive(nat_inductive),
                Declaration::Inductive(vector),
            ],
        }
    }

    /// func vector_append(T : Set, n m : Nat, a : Vector T n, b : Vector T m) -> Vector T (add n m) {
    ///     match a -> Vector T (add n m) {
    ///         Vector.Nil(T : Set) => b
    ///         Vector.Cons(T : Set, head : T, tail_length : Nat, tail : Vector T tail_length) =>
    ///             Vector.Cons(T, head, add(tail_length, m), vector_append(T, tail_length, m, tail, b))
    ///     }
    /// }
    pub fn vector_append() -> HIR {
        let vector_string = "Vector".to_string();
        let t_string = "T".to_string();
        let n_string = "n".to_string();
        let m_string = "m".to_string();
        let a_string = "a".to_string();
        let b_string = "b".to_string();
        let nat_string = "Nat".to_string();
        let natural_term = Term::Inductive(nat_string);
        let add_term = Term::Constant("add".to_string());
        let vector_term = Term::Inductive(vector_string.clone());

        let append = Term::Fixpoint {
            name: "vector_append".to_string(),
            expression_type: Box::new(Term::DependentProduct {
                parameter_name: Name::Named(t_string.clone()),
                parameter_type: Box::new(Term::Sort(Sort::Set)),
                return_type: Box::new(Term::DependentProduct {
                    parameter_name: Name::Named(n_string.clone()),
                    parameter_type: Box::new(natural_term.clone()),
                    return_type: Box::new(Term::DependentProduct {
                        parameter_name: Name::Named(m_string.clone()),
                        parameter_type: Box::new(natural_term.clone()),
                        return_type: Box::new(Term::DependentProduct {
                            parameter_name: Name::Named(a_string.clone()),
                            parameter_type: Box::new(Term::Application {
                                function: Box::new(Term::Application {
                                    function: Box::new(vector_term.clone()),
                                    argument: Box::new(Term::DeBruijnIndex(2)),
                                }),
                                argument: Box::new(Term::DeBruijnIndex(1)),
                            }),
                            return_type: Box::new(Term::DependentProduct {
                                parameter_name: Name::Named(b_string.clone()),
                                parameter_type: Box::new(Term::Application {
                                    function: Box::new(Term::Application {
                                        function: Box::new(vector_term.clone()),
                                        argument: Box::new(Term::DeBruijnIndex(3)),
                                    }),
                                    argument: Box::new(Term::DeBruijnIndex(1)),
                                }),
                                return_type: Box::new(Term::Application {
                                    function: Box::new(Term::Application {
                                        function: Box::new(vector_term.clone()),
                                        argument: Box::new(Term::DeBruijnIndex(4)),
                                    }),
                                    argument: Box::new(Term::Application {
                                        function: Box::new(Term::Application {
                                            function: Box::new(add_term.clone()),
                                            argument: Box::new(Term::DeBruijnIndex(3)),
                                        }),
                                        argument: Box::new(Term::DeBruijnIndex(2)),
                                    }),
                                }),
                            }),
                        }),
                    }),
                }),
            }),
            body: Box::new(Term::Lambda {
                name: Name::Anonymous,
                parameter_name: Name::Named(t_string),
                parameter_type: Box::new(Term::Sort(Sort::Set)),
                body: Box::new(Term::Lambda {
                    name: Name::Anonymous,
                    parameter_name: Name::Named(n_string),
                    parameter_type: Box::new(natural_term.clone()),
                    body: Box::new(Term::Lambda {
                        name: Name::Anonymous,
                        parameter_name: Name::Named(m_string),
                        parameter_type: Box::new(natural_term),
                        body: Box::new(Term::Lambda {
                            name: Name::Anonymous,
                            parameter_name: Name::Named(a_string),
                            parameter_type: Box::new(Term::Application {
                                function: Box::new(Term::Application {
                                    function: Box::new(vector_term.clone()),
                                    argument: Box::new(Term::DeBruijnIndex(2)),
                                }),
                                argument: Box::new(Term::DeBruijnIndex(1)),
                            }),
                            body: Box::new(Term::Lambda {
                                name: Name::Anonymous,
                                parameter_name: Name::Named(b_string),
                                parameter_type: Box::new(Term::Application {
                                    function: Box::new(Term::Application {
                                        function: Box::new(vector_term.clone()),
                                        argument: Box::new(Term::DeBruijnIndex(3)),
                                    }),
                                    argument: Box::new(Term::DeBruijnIndex(1)),
                                }),
                                body: Box::new(Term::Match {
                                    inductive_name: vector_string.clone(),
                                    return_type: Box::new(vector_term),
                                    scrutinee: Box::new(Term::DeBruijnIndex(1)),
                                    branches: vec![
                                        Term::DeBruijnIndex(1),
                                        Term::Application {
                                            function: Box::new(Term::Application {
                                                function: Box::new(Term::Application {
                                                    function: Box::new(Term::Application {
                                                        function: Box::new(Term::Constructor(
                                                            vector_string,
                                                            1,
                                                        )),
                                                        argument: Box::new(Term::DeBruijnIndex(3)),
                                                    }),
                                                    argument: Box::new(Term::DeBruijnIndex(2)),
                                                }),
                                                argument: Box::new(Term::Application {
                                                    function: Box::new(Term::Application {
                                                        function: Box::new(add_term),
                                                        argument: Box::new(Term::DeBruijnIndex(1)),
                                                    }),
                                                    argument: Box::new(Term::DeBruijnIndex(6)),
                                                }),
                                            }),
                                            argument: Box::new(Term::Application {
                                                function: Box::new(Term::Application {
                                                    function: Box::new(Term::Application {
                                                        function: Box::new(Term::Application {
                                                            function: Box::new(Term::Application {
                                                                function: Box::new(
                                                                    Term::DeBruijnIndex(9),
                                                                ),
                                                                argument: Box::new(
                                                                    Term::DeBruijnIndex(3),
                                                                ),
                                                            }),
                                                            argument: Box::new(
                                                                Term::DeBruijnIndex(1),
                                                            ),
                                                        }),
                                                        argument: Box::new(Term::DeBruijnIndex(6)),
                                                    }),
                                                    argument: Box::new(Term::DeBruijnIndex(0)),
                                                }),
                                                argument: Box::new(Term::DeBruijnIndex(4)),
                                            }),
                                        },
                                    ],
                                }),
                            }),
                        }),
                    }),
                }),
            }),
        };

        let mut hir = nat_add();
        hir.declarations.push(vector().declarations[1].clone());
        hir.declarations.push(Declaration::Constant(append));
        hir
    }
}
