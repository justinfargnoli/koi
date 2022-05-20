use super::ir::*;

/// enum Unit() : Set {}
pub fn unit() -> Inductive {
    Inductive {
        name: "Unit".to_string(),
        parameter_count: 0,
        typ: Term::Sort(Sort::Set),
        constructors: vec![],
    }
}

/// enum Tester() : Set {
///     Constructor(_ : Nat, _ : Nat) : Tester
/// }
pub fn two_argument_constructor() -> HIR {
    let tester_string = "Tester".to_string();
    let nat = nat();
    let nat_term = Term::Inductive(nat.name);

    let tester = Inductive {
        name: tester_string.clone(),
        parameter_count: 0,
        typ: Term::Sort(Sort::Set),
        constructors: vec![Constructor {
            name: "Constructor".to_string(),
            typ: Term::DependentProduct {
                parameter_name: Name::Anonymous,
                parameter_type: Box::new(nat_term.clone()),
                return_type: Box::new(Term::DependentProduct {
                    parameter_name: Name::Anonymous,
                    parameter_type: Box::new(nat_term),
                    return_type: Box::new(Term::Inductive(tester_string)),
                }),
            },
        }],
    };

    nat_hir().with_inductive(tester)
}

/// enum Unit(T : Set) : Set {
///     UnitConstructor : Unit T
/// }
///
/// Shouldn't type check because `UnitConstructor` doesn't take `T` as a parameter.
pub fn generic_unit() -> Inductive {
    let unit_name = "Unit".to_string();
    let t_name = "T".to_string();

    Inductive {
        name: unit_name.clone(),
        parameter_count: 0,
        typ: Term::DependentProduct {
            parameter_name: Name::Named(t_name),
            parameter_type: Box::new(Term::Sort(Sort::Set)),
            return_type: Box::new(Term::Sort(Sort::Set)),
        },
        constructors: vec![Constructor {
            name: "UnitConstructor".to_string(),
            typ: Term::Application {
                function: Box::new(Term::Inductive(unit_name)),
                argument: Box::new(Term::DeBruijnIndex(0)),
            },
        }],
    }
}

/// enum Tester() : Set {
///     Constructor() -> Tester,
/// }
pub fn single_argument_constructor2() -> Inductive {
    let tester = "Tester".to_string();
    let constructor = "Constructor".to_string();

    Inductive {
        name: tester.clone(),
        parameter_count: 0,
        typ: Term::Sort(Sort::Set),
        constructors: vec![Constructor {
            name: constructor,
            typ: Term::Inductive(tester),
        }],
    }
}

/// enum Tester() : Set {
///     Constructor(_ : Unit) -> Tester,
/// }
pub fn single_argument_constructor() -> HIR {
    let tester_name = "Tester".to_string();
    let unit = unit();

    let tester = Inductive {
        name: tester_name.clone(),
        parameter_count: 0,
        typ: Term::Sort(Sort::Set),
        constructors: vec![Constructor {
            name: "Constructor".to_string(),
            typ: Term::DependentProduct {
                parameter_name: Name::Anonymous,
                parameter_type: Box::new(Term::Inductive(unit.name.clone())),
                return_type: Box::new(Term::Inductive(tester_name)),
            },
        }],
    };

    HIR {
        declarations: vec![Declaration::Inductive(unit), Declaration::Inductive(tester)],
    }
}

/// enum Nat() : Set {
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

pub fn nat_hir() -> HIR {
    HIR {
        declarations: vec![Declaration::Inductive(nat())],
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
                            function: Box::new(Term::Constructor(nat.name, 1)),
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

    nat_hir().with_constant(add)
}

/// func identity(a : Nat) -> Nat {
///     a
/// }
pub fn nat_identity() -> HIR {
    let nat = nat();

    let identity = Term::Lambda {
        name: Name::Named("identity".to_string()),
        parameter_name: Name::Named("x".to_string()),
        parameter_type: Box::new(Term::Inductive(nat.name)),
        body: Box::new(Term::DeBruijnIndex(0)),
    };

    nat_hir().with_constant(identity)
}

/// func identity(a : Nat) -> Nat {
///     match a -> Nat {
///         Nat.Zero => Nat.Zero,
///         Nat.Successor (n : Nat) => Nat.Successor n
///     }
/// }
pub fn nat_match_identity() -> HIR {
    let nat = nat();

    let identity = Term::Lambda {
        name: Name::Named("identity".to_string()),
        parameter_name: Name::Named("x".to_string()),
        parameter_type: Box::new(Term::Inductive(nat.name.clone())),
        body: Box::new(Term::Match {
            inductive_name: nat.name.clone(),
            return_type: Box::new(Term::Inductive(nat.name.clone())),
            scrutinee: Box::new(Term::DeBruijnIndex(0)),
            branches: vec![
                Term::Constructor(nat.name.clone(), 0),
                Term::Application {
                    function: Box::new(Term::Constructor(nat.name, 1)),
                    argument: Box::new(Term::DeBruijnIndex(0)),
                },
            ],
        }),
    };

    nat_hir().with_constant(identity)
}

/// func identity(a : Nat) -> Nat {
///     match a -> Nat {
///         Nat.Zero => a,
///         Nat.Successor (n : Nat) => a
///     }
/// }
pub fn nat_match_simple() -> HIR {
    let nat = nat();

    let identity = Term::Lambda {
        name: Name::Named("identity".to_string()),
        parameter_name: Name::Named("x".to_string()),
        parameter_type: Box::new(Term::Inductive(nat.name.clone())),
        body: Box::new(Term::Match {
            inductive_name: nat.name.clone(),
            return_type: Box::new(Term::Inductive(nat.name)),
            scrutinee: Box::new(Term::DeBruijnIndex(0)),
            branches: vec![Term::DeBruijnIndex(0), Term::DeBruijnIndex(1)],
        }),
    };

    nat_hir().with_constant(identity)
}

/// func (a : Nat) -> Nat {
///     identity(a)
/// }
pub fn global_constant_use_nat_identity() -> HIR {
    let hir = nat_identity();

    let identity = Term::Lambda {
        name: Name::Anonymous,
        parameter_name: Name::Named("a".to_string()),
        parameter_type: Box::new(Term::Inductive("Nat".to_string())),
        body: Box::new(Term::Application {
            function: Box::new(Term::Constant("identity".to_string())),
            argument: Box::new(Term::DeBruijnIndex(0)),
        }),
    };

    hir.with_constant(identity)
}

/// func (_ : Nat) {
///     Nat.O
/// }
pub fn nat_zero() -> HIR {
    let nat = nat();

    let nat_term = Box::new(Term::Inductive(nat.name.clone()));

    let zero = Term::Lambda {
        name: Name::Anonymous,
        parameter_name: Name::Anonymous,
        parameter_type: nat_term,
        body: Box::new(Term::Constructor(nat.name, 0)),
    };

    nat_hir().with_constant(zero)
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
            argument: Box::new(Term::Constructor(nat.name, 0)),
        }),
    };

    nat_hir().with_constant(one)
}

/// func nat_left(left : Nat, right : Nat) {
///     left
/// }
pub fn nat_left() -> HIR {
    let nat = nat();
    let nat_term = Box::new(Term::Inductive(nat.name));

    let left = Term::Lambda {
        name: Name::Named("nat_left".to_string()),
        parameter_name: Name::Named("left".to_string()),
        parameter_type: nat_term.clone(),
        body: Box::new(Term::Lambda {
            name: Name::Anonymous,
            parameter_name: Name::Named("right".to_string()),
            parameter_type: nat_term,
            body: Box::new(Term::DeBruijnIndex(1)),
        }),
    };

    nat_hir().with_constant(left)
}

/// func rec nat_to_zero(number : Nat) -> Nat {
///     match number -> Nat {
///         Nat.O => number
///         Nat.S(n : Nat) => nat_to_zero(n)
///     }
/// }
pub fn nat_to_zero() -> HIR {
    let nat = nat();
    let nat_term = Box::new(Term::Inductive(nat.name.clone()));
    let number_string = "number".to_string();

    let nat_to_zero = Term::Fixpoint {
        expression_type: Box::new(Term::DependentProduct {
            parameter_name: Name::Named(number_string.clone()),
            parameter_type: nat_term.clone(),
            return_type: nat_term.clone(),
        }),
        body: Box::new(Term::Lambda {
            name: Name::Named("nat_to_zero".to_string()),
            parameter_name: Name::Named(number_string),
            parameter_type: nat_term.clone(),
            body: Box::new(Term::Match {
                inductive_name: nat.name,
                return_type: nat_term,
                scrutinee: Box::new(Term::DeBruijnIndex(0)),
                branches: vec![
                    Term::DeBruijnIndex(0),
                    Term::Application {
                        function: Box::new(Term::DeBruijnIndex(2)),
                        argument: Box::new(Term::DeBruijnIndex(0)),
                    },
                ],
            }),
        }),
    };

    nat_hir().with_constant(nat_to_zero)
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
    let list = list();
    let list_name = list.name.clone();
    let list_term = Term::Inductive(list_name.clone());
    let t_name = "T".to_string();
    let a_name = "a".to_string();
    let b_name = "b".to_string();

    let append = Term::Fixpoint {
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
            name: Name::Named("list_append".to_string()),
            parameter_name: Name::Named(t_name),
            parameter_type: Box::new(Term::Sort(Sort::Set)),
            body: Box::new(Term::Lambda {
                name: Name::Anonymous,
                parameter_name: Name::Named(a_name),
                parameter_type: Box::new(Term::Application {
                    function: Box::new(list_term.clone()),
                    argument: Box::new(Term::DeBruijnIndex(0)),
                }),
                body: Box::new(Term::Lambda {
                    name: Name::Anonymous,
                    parameter_name: Name::Named(b_name),
                    parameter_type: Box::new(Term::Application {
                        function: Box::new(list_term.clone()),
                        argument: Box::new(Term::DeBruijnIndex(1)),
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
                                        function: Box::new(Term::Inductive(vector_name.clone())),
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

    nat_hir().with_inductive(vector)
}

/// func vector_append(T : Set, n m : Nat, a : Vector T n, b : Vector T m) -> Vector T (add n m) {
///     match a -> Vector T (add n m) {
///         Vector.Nil(T : Set) => b
///         Vector.Cons(T : Set, head : T, tail_length : Nat, tail : Vector T tail_length) =>
///             Vector.Cons(T, head, add(tail_length, m), vector_append(T, tail_length, m, tail, b))
///     }
/// }
pub fn vector_append() -> HIR {
    let hir = nat_add();
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
            name: Name::Named("vector_append".to_string()),
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
                                return_type: Box::new(vector_term), // FIXME: This should be some application
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
                                                        argument: Box::new(Term::DeBruijnIndex(1)),
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

    hir.with_inductive(vector().get_inductive(1).clone())
        .with_constant(append)
}

pub fn undefined() -> HIR {
    HIR {
        declarations: vec![Declaration::Constant(Term::Undefined(Undefined::Empty))],
    }
}

pub fn modus_ponens() -> HIR {
    let implication_name = Name::Named("implication".to_string());
    HIR {
        declarations: vec![Declaration::Constant(Term::Lambda {
            name: Name::Named("modus_ponens".to_string()),
            parameter_name: Name::Named("P".to_string()),
            parameter_type: Box::new(Term::Sort(Sort::Prop)),
            body: Box::new(Term::Lambda {
                name: Name::Anonymous,
                parameter_name: Name::Named("Q".to_string()),
                parameter_type: Box::new(Term::Sort(Sort::Prop)),
                body: Box::new(Term::Lambda {
                    name: Name::Anonymous,
                    parameter_name: implication_name.clone(),
                    parameter_type: Box::new(Term::DependentProduct {
                        parameter_name: implication_name,
                        parameter_type: Box::new(Term::DeBruijnIndex(0)),
                        return_type: Box::new(Term::DeBruijnIndex(2)),
                    }),
                    body: Box::new(Term::Lambda {
                        name: Name::Anonymous,
                        parameter_name: Name::Anonymous,
                        parameter_type: Box::new(Term::DeBruijnIndex(2)),
                        body: Box::new(Term::Application {
                            function: Box::new(Term::DeBruijnIndex(1)),
                            argument: Box::new(Term::DeBruijnIndex(0)),
                        }),
                    }),
                }),
            }),
        })],
    }
}
