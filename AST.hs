module AST where

data AST = AST (SemanticMaps, [Class])
        deriving Show
data SemanticMaps = Maps ClassMap ImpMap ParentMap
        deriving Show

-- Data ClassMap

data ClassMap = ClassMap [MapClass]
        deriving Show
data MapClass = MapClass String [Attr]
        deriving Show
data Attr = Attr String String Expr | Attr_NI String String
        deriving Show

--Implementation Map

data ImpMap = ImpMap [ClassImp]
            deriving Show
data ClassImp = ClassImp String [MethodImp]
              deriving Show
data MethodImp = MethodImp String [String] String Expr
               deriving Show

-- Parent Map

data ParentMap = ParentMap [(String, String)]
        deriving Show

-- Misc Classes

data Class = Class Type (Maybe Type) [Feature]
        deriving (Show, Eq)

data Identifier = Ident Integer String
        deriving (Show, Eq)

data Type = Type Integer String
            deriving (Show, Eq, Ord)

data Feature = AttributeNoInit Identifier Type | AttributeInit Identifier Type Expr | Method Identifier [(Identifier, Type)] Type Expr
        deriving (Show, Eq)

data BinOp = Add | Sub | Mul | Div deriving (Show, Eq)
data CmpOp = Le | Lt | Eq deriving (Show, Eq)
data UnOp  = Not | Neg deriving (Show, Eq)

data Constant = INTS Integer | S String | Id Identifier | T | F deriving (Show, Eq)

data TyExpr = TyEx Integer String AnExpr
        deriving (Show, Eq)

data Expr = Ex Integer AnExpr | Internal String String | TypedExpr TyExpr
        deriving (Show, Eq)

data AnExpr = AssignmentEx Identifier Expr
            | DispatchEx (Maybe Expr) (Maybe Type) Identifier [Expr]
            | GDispatchEx Expr Type (Identifier) [Expr]
            | ConstantEx Constant
            | IfEx Expr Expr Expr
            | LoopEx Expr Expr
            | BlockEx [Expr]
            | NewTypeEx Type
            | IsVdEx Expr
            | BinOpEx BinOp Expr Expr
            | CmpOpEx CmpOp Expr Expr
            | UnOpEx UnOp Expr
            | LetEx [(Identifier,Type,Maybe Expr)] Expr
            | GLetEx [(Identifier,Type,Maybe Expr)] Expr
            | CaseEx Expr [(Identifier, Type, Expr)]
            | GCaseEx Expr [(Identifier, Type, Expr)]
            | Interna String
            | Dummy Int
            | Pop Int
        deriving (Show, Eq)
