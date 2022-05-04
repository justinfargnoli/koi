pub mod examples;

pub mod ir {
    #[derive(Default, Debug)]
    pub struct HIR {
        pub declarations: Vec<Declaration>,
    }

    impl HIR {
        pub fn get_constant(&self, index: usize) -> &Term {
            match self.declarations.get(index).unwrap() {
                Declaration::Constant(term) => term,
                _ => panic!(),
            }
        }

        pub fn get_inductive(&self, index: usize) -> &Inductive {
            match self.declarations.get(index).unwrap() {
                Declaration::Inductive(inductive) => inductive,
                _ => panic!(),
            }
        }

        pub fn with(mut self, declaration: Declaration) -> HIR {
            self.declarations.push(declaration);
            self
        }

        pub fn with_inductive(self, inductive: Inductive) -> HIR {
            self.with(Declaration::Inductive(inductive))
        }

        pub fn with_constant(self, constant: Term) -> HIR {
            self.with(Declaration::Constant(constant))
        }
    }

    #[derive(Debug, Clone)]
    pub enum Declaration {
        Constant(Term),
        Inductive(Inductive),
    }

    #[derive(Clone, Debug)]
    pub struct Inductive {
        pub name: String,
        pub parameter_count: usize,
        pub typ: Term,
        pub constructors: Vec<Constructor>,
    }

    #[derive(Clone, Debug)]
    pub struct Constructor {
        pub name: String,
        pub typ: Term,
    }

    type BranchesCount = usize;
    pub type DeBruijnIndex = usize;

    pub fn debruijn_index_lookup<T: std::fmt::Debug>(
        slice: &[T],
        debruijn_index: DeBruijnIndex,
    ) -> &T {
        &slice[slice.len() - 1 - debruijn_index]
    }

    pub fn debruijn_index_lookup_mut<T>(slice: &mut [T], debruijn_index: DeBruijnIndex) -> &mut T {
        &mut slice[slice.len() - 1 - debruijn_index]
    }

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
            expression_type: Box<Term>,
            body: Box<Term>,
        },
        Undefined(Undefined),
    }

    impl Term {
        pub fn is_sort(term: &Term) -> bool {
            matches!(term, Term::Sort(_))
        }
    }

    #[derive(Clone, Debug, PartialEq)]
    pub enum Name {
        Anonymous,
        Named(String),
    }

    #[derive(Clone, Debug, PartialEq)]
    pub enum Sort {
        Prop,
        Set,
        Type(u32),
    }

    #[derive(Clone, Debug, PartialEq)]
    pub enum Undefined {
        CodegenInnerConstructorFunction {
            constructor_index: u8,
            inductive_name: String,
            constructor_parameter_count: usize,
        },
        Empty,
    }
}
