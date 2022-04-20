pub mod ir {
    use universe::{Universe, UniverseInstance};

    #[derive(Default)]
    pub struct HIR {
        pub declarations: Vec<Declaration>,
    }

    pub enum Declaration {
        Constant(Term),
        Inductive(Inductive),
    }

    pub type Identifier = String;

    #[derive(Clone)]
    pub struct Inductive {
        pub name: Identifier,
        pub parameters: Vec<Term>,
        pub arity: Term,
        pub constructors: Vec<Constructor>,
    }

    #[derive(Clone)]
    pub struct Constructor {
        pub name: Identifier,
        pub typ: Term,
    }

    pub type DeBruijnIndex = usize;
    type BranchesCount = usize;

    #[derive(Clone, Debug, PartialEq)]
    pub enum Term {
        DeBruijnIndex(DeBruijnIndex),
        Sort(Universe),
        DependentProduct {
            parameter_name: Name,
            parameter_type: Box<Term>,
            return_type: Box<Term>,
        },
        Lambda {
            parameter_name: Name,
            parameter_type: Box<Term>, // The type of the argument to the function
            body: Box<Term>,
        },
        Let {
            name: Name,
            expression: Box<Term>,
            expression_type: Box<Term>,
            then: Box<Term>,
        },
        Application {
            function: Box<Term>,
            argument: Box<Term>,
        },
        Constant(String, UniverseInstance),
        Inductive(String, UniverseInstance),
        Constructor(String, BranchesCount, UniverseInstance),
        Match {
            inductive_name: String,
            parameter_count: BranchesCount, // NOTE: likely don't need
            return_type: Box<Term>,
            scrutinee: Box<Term>,
            branches: Vec<(BranchesCount, Term)>, // QUESTION: Can `BranchesCount` be removed here and we just use the position in the `Vec`?
        },
        Fixpoint {
            fixpoint_name: Name,
            fixpoint_type: Box<Term>,
            body: Box<Term>,
            recursive_parameter_index: usize,
        },
    }

    #[derive(Clone, Debug, PartialEq)]
    pub enum Name {
        Anonymous,
        Named(Identifier),
    }

    pub mod universe {
        use super::DeBruijnIndex;

        #[derive(Clone, Debug, PartialEq)]
        pub struct Universe(Vec<Expression>); // Vec must be non-empty

        impl Universe {
            pub fn build_one(expression: Expression) -> Universe {
                Universe(vec![expression])
            }

            fn is_prop(&self) -> bool {
                self.0.iter().all(|expression| expression.is_prop())
            }

            pub fn sort_of_product(from_sort: &Self, to_sort: &Self) -> Self {
                if to_sort.is_prop() {
                    to_sort.clone()
                } else {
                    Self::supremum(from_sort, to_sort)
                }
            }

            pub fn supremum(&self, other: &Self) -> Self {
                let mut sup = self.0.clone();
                sup.append(&mut other.0.clone());
                Universe(sup)
            }

            pub fn length(&self) -> usize {
                self.0.len()
            }

            pub fn first(&self) -> &Expression {
                self.0.first().unwrap()
            }

            pub fn representative_expression(&self) -> &Expression {
                let mut iterator = self.0.iter();
                let expression = iterator.next().unwrap();
                iterator.for_each(|expr| assert_eq!(expr, expression));
                expression
            }
        }

        #[derive(Clone, Debug, PartialEq)]
        pub struct Expression(Level, pub bool);

        impl Expression {
            pub fn build(level: Level, plus_one: bool) -> Expression {
                Expression(level, plus_one)
            }

            pub fn level(&self) -> &Level {
                &self.0
            }

            pub fn is_prop(&self) -> bool {
                matches!(self, Expression(Level::Prop, _))
            }

            pub fn type_1() -> Expression {
                Expression(Level::Set, true)
            }

            pub fn successor(&self) -> Self {
                match self {
                    Expression(level, false) => Expression(level.clone(), true),
                    _ => panic!(),
                }
            }

            pub fn set() -> Expression {
                Expression(Level::Set, false)
            }
        }

        #[derive(Clone, Debug, PartialEq)]
        pub struct UniverseInstance(Vec<Level>);

        impl UniverseInstance {
            pub fn empty() -> UniverseInstance {
                UniverseInstance(Vec::new())
            }
        }

        #[derive(Clone, Debug, PartialEq)]
        pub enum Level {
            Prop,
            Set,
            Level(String),
            DeBruijnIndex(DeBruijnIndex),
        }
    }
}

pub mod examples {
    use super::ir::{universe::*, *};

    /// enum Unit() : Type 0 {}
    pub fn unit() -> Inductive {
        Inductive {
            name: "Unit".to_string(),
            parameters: Vec::new(),
            arity: Term::Sort(Universe::build_one(Expression::set())),
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
            parameters: Vec::new(),
            arity: Term::Sort(Universe::build_one(Expression::set())),
            constructors: vec![
                Constructor {
                    name: zero,
                    typ: Term::Inductive(natural.clone(), UniverseInstance::empty()),
                },
                Constructor {
                    name: successor,
                    typ: Term::DependentProduct {
                        parameter_name: Name::Anonymous,
                        parameter_type: Box::new(Term::Inductive(
                            natural.clone(),
                            UniverseInstance::empty(),
                        )),
                        return_type: Box::new(Term::Inductive(natural, UniverseInstance::empty())),
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

        let nat_term = Box::new(Term::Inductive(nat.name.clone(), UniverseInstance::empty()));
        let a = Name::Named("a".to_string());
        let b = Name::Named("b".to_string());

        let add = Term::Fixpoint {
            fixpoint_name: Name::Named("add".to_string()),
            fixpoint_type: Box::new(Term::DependentProduct {
                parameter_name: a.clone(),
                parameter_type: nat_term.clone(),
                return_type: Box::new(Term::DependentProduct {
                    parameter_name: b.clone(),
                    parameter_type: nat_term.clone(),
                    return_type: nat_term.clone(),
                }),
            }),
            body: Box::new(Term::Lambda {
                parameter_name: a.clone(),
                parameter_type: nat_term.clone(),
                body: Box::new(Term::Lambda {
                    parameter_name: b,
                    parameter_type: nat_term.clone(),
                    body: Box::new(Term::Match {
                        inductive_name: nat.name.clone(),
                        parameter_count: 0,
                        return_type: nat_term.clone(),
                        scrutinee: Box::new(Term::DeBruijnIndex(1)),
                        branches: vec![
                            (0, Term::DeBruijnIndex(0)),
                            (
                                1,
                                Term::Application {
                                    function: Box::new(Term::Constructor(
                                        nat.name.clone(),
                                        1,
                                        UniverseInstance::empty(),
                                    )),
                                    argument: Box::new(Term::Application {
                                        function: Box::new(Term::Application {
                                            function: Box::new(Term::DeBruijnIndex(3)),
                                            argument: Box::new(Term::DeBruijnIndex(0)),
                                        }),
                                        argument: Box::new(Term::DeBruijnIndex(1)),
                                    }),
                                },
                            ),
                        ],
                    }),
                }),
            }),
            recursive_parameter_index: 0,
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

        let nat_term = Box::new(Term::Inductive(nat.name.clone(), UniverseInstance::empty()));
        let a = Name::Named("a".to_string());

        let identity = Term::Lambda {
            parameter_name: Name::Named("identity".to_string()),
            parameter_type: Box::new(Term::DependentProduct {
                parameter_name: a,
                parameter_type: nat_term.clone(),
                return_type: nat_term,
            }),
            body: Box::new(Term::DeBruijnIndex(0)),
        };

        HIR {
            declarations: vec![Declaration::Inductive(nat), Declaration::Constant(identity)],
        }
    }

    /// func (_ : Nat) {
    ///     Nat.S(Nat.O)
    /// }
    pub fn nat_zero() -> HIR {
        let nat = nat();

        let nat_term = Box::new(Term::Inductive(nat.name.clone(), UniverseInstance::empty()));

        let zero = Term::Lambda {
            parameter_name: Name::Anonymous,
            parameter_type: nat_term,
            body: Box::new(Term::Constructor(
                nat.name.clone(),
                0,
                UniverseInstance::empty(),
            )),
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

        let nat_term = Box::new(Term::Inductive(nat.name.clone(), UniverseInstance::empty()));

        let one = Term::Lambda {
            parameter_name: Name::Anonymous,
            parameter_type: nat_term,
            body: Box::new(Term::Application {
                function: Box::new(Term::Constructor(
                    nat.name.clone(),
                    1,
                    UniverseInstance::empty(),
                )),
                argument: Box::new(Term::Constructor(
                    nat.name.clone(),
                    0,
                    UniverseInstance::empty(),
                )),
            }),
        };

        HIR {
            declarations: vec![Declaration::Inductive(nat), Declaration::Constant(one)],
        }
    }
}
