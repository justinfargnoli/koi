pub struct HIR {
    declarations: Vec<Term>,
    inductives: Vec<Inductive>,
}

type Identifier = String;

pub struct Inductive {
    name: Identifier,
    parameters: Vec<Term>,
    arity: Term,
    constructors: Vec<Constructor>,
}

pub struct Constructor {
    name: Identifier,
    typ: Term,
}

type DeBruijnIndex = u32;
type BranchesCount = u32;
type Universe = Vec<(Level, bool)>; // Vec must be non-empty
type UniverseInstance = Vec<Level>;

pub enum Term {
    DeBruijnIndex(DeBruijnIndex),
    Sort(Universe),
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
    Inductive(String, UniverseInstance),
    Constructor(String, BranchesCount, UniverseInstance),
    Match {
        inductive_name: String,
        parameter_count: BranchesCount,
        typ: Box<Term>,
        discriminee: Box<Term>,
        branches: Vec<(BranchesCount, Term)>, // QUESTION: Can `BranchesCount` be removed here and we just use the position in the `Vec`?
    },
    Fixpoint {
        name: Name,
        typ: Box<Term>,
        body: Box<Term>,
        recursive_parameter_index: u32,
    },
}

pub enum Name {
    Anonymous,
    Named(Identifier),
}

pub enum Level {
    Prop, 
    Set,
    Level(String),
    DeBruijnIndex(DeBruijnIndex),
}
