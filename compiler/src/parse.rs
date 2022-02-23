mod ast {
    pub struct AST {
        declarations: Vec<Declaration>,
    }

    pub enum Declaration {
        Enum(Enum),
        Func(Func),
        Comment(String),
    }

    pub enum Expression {
        Name(String),
        // Dependent Product
        Let(Let),
        FunctionCall(FunctionCall),
        Match(Match),
        // Constructor
        Declaration(Declaration),
    }

    pub struct Enum {
        name: String,
        parameters: Vec<Parameter>,
        indexed_by: Vec<Parameter>,
        return_type: Box<Expression>,
        variants: Vec<Variant>,
    }

    pub struct Parameter {
        name: Name,
        typ: Expression,
    }

    pub enum Name {
        Anonymous,
        Name(String),
        Constructor(ConstructorName),
    }

    pub struct ConstructorName {
        enumeration: String,
        variant: String,
    }

    pub struct Variant {
        name: String,
        parameters: Vec<Parameter>,
        indexes: Vec<Parameter>,
        return_type: Expression,
    }

    pub struct Func {
        name: Name,
        recursive: bool,
        parameters: Vec<Parameter>,
        return_type: Box<Expression>,
        body: Box<Expression>,
    }

    pub struct Match {
        scrutinee_name: String,
        return_type: Box<Expression>,
        arms: Vec<Arm>,
    }

    pub struct Arm {
        name: ConstructorName,
        parameters: Vec<Parameter>,
        body: Expression,
    }

    pub struct Let {
        name: String,
        typ: Box<Expression>,
        expression: Box<Expression>,
        then: Box<Expression>,
    }

    pub struct FunctionCall {
        function: Box<Expression>,
        arguments: Vec<Expression>,
    }
}
