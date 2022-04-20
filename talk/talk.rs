struct Inductive {
    name: Name,
    parameters: Vec<Term>,
    arity: Term,
    constructors: Vec<Constructor>,
}

struct Constructor {
    name: String,
    typ: Term,
}

enum Term {
    Inductive(String),
    Constructor(String, u8),
    Lambda {
        parameter_name: String,
        parameter_type: Term,
        body: Term,
    },
    Fixpoint {
        fixpoint_name: String,
        fixpoint_type: Term,
        body: Term,
        recursive_parameter_index: u32,
    },
    Constant(String),
    DependentProduct {
        parameter_name: String,
        parameter_type: Term,
        return_type: Term,
    },
    Sort(Universe),
    Application {
        function: Term,
        argument: Term,
    },
    Let {
        name: String,
        expression: Term,
        expression_type: Term,
        then: Term,
    },
    DeBruijnIndex(u32),
    Match {
        inductive_name: String,
        scrutinee: Term,
        return_type: Term,
        branches: Vec<(u8, Term)>,
    },
}

Match {
    inductive_name : "Natural",
    scrutinee: /* `a` */
    return_type: Inductive("Natural"),
    branches: [
        (0, /* `b` */),
        (1, /* Successor add n b */)
    ]
}

Match {
    inductive_name : "Natural",
    scrutinee: DeBruijnIndex(1)
    return_type: Inductive("Natural"),
    branches: [
        (0, DeBruijnIndex(0)),
        (1, /* Successor (n : Natural) => 
                Successor (add */ 
                    DeBruijnIndex(0)
                    DeBruijnIndex(1)
                /* ) */
        )
    ]
}

(1, /* Successor (n : Natural) => */
    Application {
        function: Constructor("Natural", 1)
        argument: Application {
            function: Application {
                function: Constant("add")
                argument: DeBruijnIndex(0)
            argument: DeBruijnIndex(1)                     
    }
)

Lambda {
    parameter_name: "a",
    parameter_type: /* Natural */,
    body: Lambda {
        parameter_name: "b",
        parameter_type: /* Natural */,
        body: /* add `a` and `b`*/
    },
}

Inductive {
    name: "Natural",
    parameters: [],
    arity: Sort(Universe::Set),
    constructors: [
        Constructor {
            name: "Zero",
            typ: Inductive("Natural"),
        },
        Constructor {
            name: "Successor",
            typ: DependentProduct {
                parameter_name: "n",
                parameter_type: Inductive("Natural"),
                return_type: Inductive("Natural"),
            }
        }
    ],
}

Lambda {
    parameter_name: "a",
    parameter_type: Inductive("Natural"),
    body: Lambda {
        parameter_name: "b",
        parameter_type: Inductive("Natural"),
        body: Match {
            inductive_name : "Natural",
            scrutinee: DeBruijnIndex(1)
            return_type: Inductive("Natural"),
            branches: [
                (0, DeBruijnIndex(0)),
                (1, /* Successor (n : Natural) => */
                    Application {
                        function: Constructor("Natural", 1)
                        argument: Application {
                            function: Application {
                                function: Constant("add")
                                argument: DeBruijnIndex(0)
                            argument: DeBruijnIndex(1)})]}}}

// Natural

Inductive {
    name: "Natural",
    parameters: [],
    arity: Sort(Universe::Set),
    constructors: [
        Constructor {
            name: "Zero",
            typ: Inductive("Natural"),
        },
        Constructor {
            name: "Successor",
            typ: DependentProduct {
                parameter_name: "n",
                parameter_type: Inductive("Natural"),
                return_type: Inductive("Natural"),
            }
        }
    ],
}

DependentProduct {
    parameter_name: "a",
    parameter_type: Inductive("Natural"),
    return_type: DependentProduct {
        parameter_name: "b",
        parameter_type: Inductive("Natural"),
        return_type: Inductive("Natural"),
    }
}

Application {
    function: Application {
        function: Constant("add"),
        argument: Constructor("Natural", 0),
    },
    argument: Constructor("Natural", 0),
}



