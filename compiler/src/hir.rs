pub mod ir {
    use universe::{Universe, UniverseInstance};

    pub struct HIR {
        pub declarations: Vec<Declaration>,
    }

    impl HIR {
        pub fn new() -> HIR {
            HIR {
                declarations: Vec::new(),
            }
        }
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
            arguments: Vec<Term>,
        },
        Constant(String, UniverseInstance),
        Inductive(String, UniverseInstance),
        Constructor(String, BranchesCount, UniverseInstance),
        Match {
            inductive_name: String,
            parameter_count: BranchesCount,
            type_info: Box<Term>,
            discriminee: Box<Term>,
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
                match self {
                    Expression(Level::Prop, _) => true,
                    _ => false,
                }
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
