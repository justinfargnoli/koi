mod ir {
    use crate::hir::ir::Identifier;

    pub struct AST {
        declarations: Vec<Declaration>,
    }

    pub enum Declaration {
        Enum(Enum),
        Func(Func),
        Let(Let),
        Comment(String),
    }

    pub enum Expression {
        Identifier(Identifier),
        // Sort
        // Dependent Product
        Func(Func),
        Let(Let),
        FunctionCall(FunctionCall),
        // Constant - UniverseInstance?
        // Inductive - UniverseInstance?
        Constructor(ConstructorIdentifier), // UniverseInstance?
        Match(Match),
        Comment(String, Box<Expression>),
    }

    pub struct Enum {
        name: Identifier,
        parameters: Vec<Expression>,
        arity: Box<Expression>,
        constructors: Vec<Constructor>,
    }

    pub struct Constructor {
        name: Identifier,
        parameters: Vec<Expression>,
        return_type: Expression,
    }

    pub struct Func {
        name: Name,
        recursive: bool,
        typ: Box<Expression>,
        body: Box<Expression>,
    }

    pub enum Name {
        Anonymous,
        Name(Identifier),
    }

    pub struct Let {
        name: Identifier,
        expression: Box<Expression>,
        expression_type: Box<Expression>,
        then: Box<Expression>,
    }

    pub struct FunctionCall {
        function: Box<Expression>,
        arguments: Vec<Expression>,
    }

    pub struct ConstructorIdentifier {
        enumeration: Identifier,
        variant: Identifier,
    }

    pub struct Match {
        discriminee: Box<Expression>,
        expression_type: Box<Expression>,
        arms: Vec<(ConstructorIdentifier, Expression)>,
    }
}
