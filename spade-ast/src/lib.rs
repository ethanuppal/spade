use comptime::{ComptimeCondition, MaybeComptime};
use num::{BigInt, BigUint, Zero};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Path},
    num_ext::InfallibleToBigInt,
};

pub mod comptime;
pub mod testutil;

#[derive(PartialEq, Debug, Clone)]
pub enum TypeExpression {
    TypeSpec(Box<Loc<TypeSpec>>),
    Integer(BigUint),
}
impl WithLocation for TypeExpression {}

/// A specification of a type to be used. For example, the types of input/output arguments the type
/// of fields in a struct etc.
#[derive(PartialEq, Debug, Clone)]
pub enum TypeSpec {
    Tuple(Vec<Loc<TypeSpec>>),
    Array {
        inner: Box<Loc<TypeSpec>>,
        size: Box<Loc<TypeExpression>>,
    },
    Named(Loc<Path>, Option<Loc<Vec<Loc<TypeExpression>>>>),
    Unit(Loc<()>),
    /// A type in which signals travel in the opposite direction to normal. Any type containing a
    /// Backward type is considered a port, meaning it can not be explicitly put in registers, and
    /// is not registered in pipelines
    Backward(Box<Loc<TypeSpec>>),
    Wire(Box<Loc<TypeSpec>>),
}
impl WithLocation for TypeSpec {}

#[derive(PartialEq, Debug, Clone)]
pub enum ArgumentPattern {
    Named(Vec<(Loc<Identifier>, Option<Loc<Pattern>>)>),
    Positional(Vec<Loc<Pattern>>),
}
impl WithLocation for ArgumentPattern {}

#[derive(PartialEq, Debug, Clone)]
pub enum Pattern {
    Integer(IntLiteral),
    Bool(bool),
    Path(Loc<Path>),
    Tuple(Vec<Loc<Pattern>>),
    Type(Loc<Path>, Loc<ArgumentPattern>),
}
impl WithLocation for Pattern {}

// Helper constructors for writing neater tests
impl Pattern {
    pub fn integer(val: i32) -> Self {
        Pattern::Integer(IntLiteral::Signed(val.to_bigint()))
    }
    pub fn name(name: &str) -> Loc<Self> {
        Pattern::Path(Path(vec![Identifier(name.to_string()).nowhere()]).nowhere()).nowhere()
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum NamedArgument {
    Full(Loc<Identifier>, Loc<Expression>),
    /// Binds a local variable to an argument with the same name
    Short(Loc<Identifier>),
}
impl WithLocation for NamedArgument {}

#[derive(PartialEq, Debug, Clone)]
pub enum ArgumentList {
    Positional(Vec<Loc<Expression>>),
    Named(Vec<NamedArgument>),
}
impl WithLocation for ArgumentList {}

#[derive(PartialEq, Debug, Clone)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Equals,
    Lt,
    Gt,
    Le,
    Ge,
    LogicalAnd,
    LogicalOr,
    LogicalXor,
    LeftShift,
    RightShift,
    ArithmeticRightShift,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
}

#[derive(PartialEq, Debug, Clone)]
pub enum UnaryOperator {
    Sub,
    Not,
    BitwiseNot,
    Dereference,
    Reference,
}
impl WithLocation for UnaryOperator {}

#[derive(PartialEq, Debug, Clone)]
pub enum PipelineStageReference {
    Relative(Loc<BigInt>),
    Absolute(Loc<Identifier>),
}

#[derive(PartialEq, Debug, Clone)]
pub enum CallKind {
    Function,
    Entity(Loc<()>),
    Pipeline(Loc<()>, Loc<MaybeComptime<Loc<IntLiteral>>>),
}
impl WithLocation for CallKind {}

#[derive(PartialEq, Debug, Clone)]
pub enum Expression {
    Identifier(Loc<Path>),
    IntLiteral(IntLiteral),
    BoolLiteral(bool),
    ArrayLiteral(Vec<Loc<Expression>>),
    Index(Box<Loc<Expression>>, Box<Loc<Expression>>),
    TupleLiteral(Vec<Loc<Expression>>),
    TupleIndex(Box<Loc<Expression>>, Loc<u128>),
    FieldAccess(Box<Loc<Expression>>, Loc<Identifier>),
    Call {
        kind: CallKind,
        callee: Loc<Path>,
        args: Loc<ArgumentList>,
    },
    MethodCall {
        target: Box<Loc<Expression>>,
        name: Loc<Identifier>,
        args: Loc<ArgumentList>,
        kind: CallKind,
    },
    If(
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
    ),
    Match(
        Box<Loc<Expression>>,
        Loc<Vec<(Loc<Pattern>, Loc<Expression>)>>,
    ),
    UnaryOperator(UnaryOperator, Box<Loc<Expression>>),
    BinaryOperator(Box<Loc<Expression>>, BinaryOperator, Box<Loc<Expression>>),
    Block(Box<Block>),
    /// E.g. `stage(-5).x`, `stage('b).y`
    PipelineReference {
        /// ```text
        /// stage(-5).xyz
        /// ^^^^^^^^^
        /// ```
        stage_kw_and_reference_loc: Loc<()>,
        /// ```text
        /// stage(-5).xyz
        ///       ^^
        /// ```
        stage: PipelineStageReference,
        /// ```text
        /// stage(-5).xyz
        ///           ^^^
        /// ```
        name: Loc<Identifier>,
    },
    Comptime(Box<Loc<ComptimeCondition<Loc<Expression>>>>),
}
impl WithLocation for Expression {}

impl Expression {
    pub fn int_literal(val: i32) -> Self {
        Self::IntLiteral(IntLiteral::Signed(val.to_bigint()))
    }

    pub fn assume_block(&self) -> &Block {
        if let Expression::Block(inner) = self {
            inner
        } else {
            panic!("Expected block")
        }
    }

    pub fn variant_str(&self) -> &'static str {
        match self {
            Expression::Identifier(_) => "identifier",
            Expression::IntLiteral(_) => "int literal",
            Expression::BoolLiteral(_) => "bool literal",
            Expression::ArrayLiteral(_) => "array literal",
            Expression::Index(_, _) => "index",
            Expression::TupleLiteral(_) => "tuple literal",
            Expression::TupleIndex(_, _) => "tuple index",
            Expression::FieldAccess(_, _) => "field access",
            Expression::If(_, _, _) => "if",
            Expression::Match(_, _) => "match",
            Expression::Call { .. } => "call",
            Expression::MethodCall { .. } => "method call",
            Expression::UnaryOperator(_, _) => "unary operator",
            Expression::BinaryOperator(_, _, _) => "binary operator",
            Expression::Block(_) => "block",
            Expression::PipelineReference { .. } => "pipeline reference",
            Expression::Comptime { .. } => "comptime",
        }
    }
}

/// An integer literal, which may or may not have been suffixed with `U` to indicate
/// it being an unsigned literal.
#[derive(PartialEq, Debug, Clone)]
pub enum IntLiteral {
    Signed(BigInt),
    Unsigned(BigUint),
}
impl WithLocation for IntLiteral {}

impl IntLiteral {
    pub fn signed(val: i32) -> IntLiteral {
        IntLiteral::Signed(val.to_bigint())
    }

    /// Returns this number as a signed number. Unsigned numbers are losslessly converted to
    /// signed
    pub fn as_signed(self) -> BigInt {
        match self {
            IntLiteral::Signed(val) => val,
            // NOTE: Safe unwrap. This can't fail
            IntLiteral::Unsigned(val) => val.to_bigint(),
        }
    }

    // Returns the signed, or unsigned number as a BigUint if it is positive, otherwise,
    // None
    pub fn as_unsigned(self) -> Option<BigUint> {
        match self {
            IntLiteral::Signed(val) => {
                if val >= BigInt::zero() {
                    Some(val.to_biguint().unwrap())
                } else {
                    None
                }
            }
            IntLiteral::Unsigned(val) => Some(val),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Block {
    pub statements: Vec<Loc<Statement>>,
    pub result: Loc<Expression>,
}
impl WithLocation for Block {}

#[derive(PartialEq, Debug, Clone)]
pub enum Statement {
    Label(Loc<Identifier>),
    Declaration(Vec<Loc<Identifier>>),
    Binding(Loc<Pattern>, Option<Loc<TypeSpec>>, Loc<Expression>),
    PipelineRegMarker(usize),
    Register(Loc<Register>),
    /// Sets the value of the target expression, which must be a Backward port to
    /// the value of `value`
    Set {
        target: Loc<Expression>,
        value: Loc<Expression>,
    },
    Assert(Loc<Expression>),
    Comptime(ComptimeCondition<Vec<Loc<Statement>>>),
}
impl WithLocation for Statement {}

/// A generic type parameter
#[derive(PartialEq, Debug, Clone)]
pub enum TypeParam {
    TypeName(Loc<Identifier>),
    Integer(Loc<Identifier>),
}
impl WithLocation for TypeParam {}
impl TypeParam {
    pub fn name(&self) -> &Loc<Identifier> {
        match self {
            TypeParam::TypeName(n) => n,
            TypeParam::Integer(n) => n,
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct AttributeList(pub Vec<Loc<Identifier>>);
impl AttributeList {
    pub fn empty() -> Self {
        Self(vec![])
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct ParameterList {
    pub self_: Option<Loc<()>>,
    pub args: Vec<(Loc<Identifier>, Loc<TypeSpec>)>,
}
impl WithLocation for ParameterList {}

impl ParameterList {
    pub fn without_self(args: Vec<(Loc<Identifier>, Loc<TypeSpec>)>) -> Self {
        Self { self_: None, args }
    }

    pub fn with_self(self_: Loc<()>, args: Vec<(Loc<Identifier>, Loc<TypeSpec>)>) -> Self {
        Self {
            self_: Some(self_),
            args,
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum UnitKind {
    Function,
    Entity,
    Pipeline(Loc<MaybeComptime<Loc<IntLiteral>>>),
}
impl WithLocation for UnitKind {}

impl UnitKind {
    pub fn is_pipeline(&self) -> bool {
        match self {
            UnitKind::Function => false,
            UnitKind::Entity => false,
            UnitKind::Pipeline(_) => true,
        }
    }
}

impl std::fmt::Display for UnitKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnitKind::Function => write!(f, "fn"),
            UnitKind::Entity => write!(f, "entity"),
            UnitKind::Pipeline(_) => write!(f, "pipeline"),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Unit {
    pub attributes: AttributeList,
    pub unit_kind: Loc<UnitKind>,
    pub name: Loc<Identifier>,
    pub inputs: Loc<ParameterList>,
    pub output_type: Option<Loc<TypeSpec>>,
    /// The body is an expression for ID assignment purposes, but semantic analysis
    /// ensures that it is always a block. If body is `None`, the entity is __builtin__
    pub body: Option<Loc<Expression>>,
    pub type_params: Vec<Loc<TypeParam>>,
}
impl WithLocation for Unit {}

/// A definition of a function without a body.
#[derive(PartialEq, Debug, Clone)]
pub struct FunctionDecl {
    pub name: Loc<Identifier>,
    pub inputs: Loc<ParameterList>,
    pub return_type: Option<Loc<TypeSpec>>,
    pub type_params: Vec<Loc<TypeParam>>,
}
impl WithLocation for FunctionDecl {}

#[derive(PartialEq, Debug, Clone)]
pub struct Register {
    pub pattern: Loc<Pattern>,
    pub clock: Loc<Expression>,
    pub reset: Option<(Loc<Expression>, Loc<Expression>)>,
    pub value: Loc<Expression>,
    pub value_type: Option<Loc<TypeSpec>>,
}
impl WithLocation for Register {}

/// A definition of a trait
#[derive(PartialEq, Debug, Clone)]
pub struct TraitDef {
    pub name: Loc<Identifier>,
    pub functions: Vec<Loc<FunctionDecl>>,
}
impl WithLocation for TraitDef {}

#[derive(PartialEq, Debug, Clone)]
pub struct ImplBlock {
    pub r#trait: Option<Loc<Path>>,
    pub target: Loc<Path>,
    pub units: Vec<Loc<Unit>>,
}
impl WithLocation for ImplBlock {}

/// Declaration of an enum
#[derive(PartialEq, Debug, Clone)]
pub struct Enum {
    pub name: Loc<Identifier>,
    pub options: Vec<(Loc<Identifier>, Option<Loc<ParameterList>>)>,
}
impl WithLocation for Enum {}

#[derive(PartialEq, Debug, Clone)]
pub struct Struct {
    pub name: Loc<Identifier>,
    pub members: Loc<ParameterList>,
    pub port_keyword: Option<Loc<()>>,
}
impl WithLocation for Struct {}

impl Struct {
    pub fn is_port(&self) -> bool {
        self.port_keyword.is_some()
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeDeclKind {
    Enum(Loc<Enum>),
    Struct(Loc<Struct>),
}

/// A declaration of a new type
#[derive(PartialEq, Debug, Clone)]
pub struct TypeDeclaration {
    pub name: Loc<Identifier>,
    pub kind: TypeDeclKind,
    pub generic_args: Vec<Loc<TypeParam>>,
}
impl WithLocation for TypeDeclaration {}

#[derive(PartialEq, Debug, Clone)]
pub struct UseStatement {
    pub path: Loc<Path>,
    pub alias: Option<Loc<Identifier>>,
}
impl WithLocation for UseStatement {}

#[derive(PartialEq, Debug, Clone)]
pub struct ComptimeConfig {
    pub name: Loc<Identifier>,
    pub val: Loc<BigInt>,
}
impl WithLocation for ComptimeConfig {}

/// Items are things typically present at the top level of a module such as
/// entities, pipelines, submodules etc.
#[derive(PartialEq, Debug, Clone)]
pub enum Item {
    Unit(Loc<Unit>),
    TraitDef(Loc<TraitDef>),
    Type(Loc<TypeDeclaration>),
    Module(Loc<Module>),
    Use(Loc<UseStatement>),
    Config(Loc<ComptimeConfig>),
    ImplBlock(Loc<ImplBlock>),
}
impl WithLocation for Item {}

impl Item {
    pub fn name(&self) -> Option<&Identifier> {
        match self {
            Item::Unit(u) => Some(&u.name.inner),
            Item::TraitDef(t) => Some(&t.name.inner),
            Item::Type(t) => Some(&t.name.inner),
            Item::Module(m) => Some(&m.name.inner),
            Item::Use(u) => u.alias.as_ref().map(|name| &name.inner),
            Item::Config(c) => Some(&c.name.inner),
            Item::ImplBlock(_) => None,
        }
    }

    pub fn variant_str(&self) -> &'static str {
        match self {
            Item::Unit(_) => "unit",
            Item::TraitDef(_) => "trait definition",
            Item::Type(_) => "type",
            Item::Module(_) => "module",
            Item::Use(_) => "use",
            Item::Config(_) => "config",
            Item::ImplBlock(_) => "impl",
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Module {
    pub name: Loc<Identifier>,
    pub body: Loc<ModuleBody>,
}
impl WithLocation for Module {}

#[derive(PartialEq, Debug, Clone)]
pub struct ModuleBody {
    pub members: Vec<Item>,
}
impl WithLocation for ModuleBody {}
