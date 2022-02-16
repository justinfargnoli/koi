pub struct HIR {
    global_terms: Vec<Term>,
}

type DeBruijnIndex = u32;
type BranchesCount = u16;

pub enum Term {
    DeBruijnIndex(DeBruijnIndex),
    Sort(Universe),
    Cast {
        term: Box<Term>,
        typ: Box<Term>,
    },
    DependentProduct {
        name: Name,
        from_type: Box<Term>,
        to_type: Box<Term>,
    },
    Lambda {
        name: Name,
        typ: Box<Term>,
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
    Inductive(Inductive, UniverseInstance),
    Constructor(Inductive, BranchesCount, UniverseInstance),
    Match {
        inductive: Inductive,
        parameter_count: BranchesCount,
        typ: Box<Term>,
        discriminee: Box<Term>,
        branches: Vec<(BranchesCount, Term)>,
    },
    Fixpoint(Box<Term>, DeBruijnIndex), // Unsure on this one
}

pub enum Name {
    Anonymous,
    Named(String),
}

pub struct Universe {}

pub struct UniverseInstance {}

pub struct Inductive {}
