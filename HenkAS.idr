module HenkAS

%default total
%access public export

-- Abstract Syntax --

-- Literals
data Lit = LitInt Int | IntType
  -- deriving (Show,Eq)

-- Sorts
data Sort = Star | Box | SortNum Int
  -- deriving (Show,Eq)

-- Variable
data Variable = Var String | Anonymous
  -- deriving (Show,Eq)

mutual
  -- Typed Variable
  data TVariable = TVar Variable Expr
  -- deriving (Show,Eq)

  -- Expression
  data Expr
    = LamExpr TVariable Expr          -- Lambda Abstraction
    | PiExpr TVariable Expr           -- Pi
    | AppExpr Expr Expr               -- Application
    | CaseExpr Expr (List Alt) Expr   -- Case
    | VarExpr TVariable               -- Typed Variable
    | LitExpr Lit                     -- Literal
    | SortExpr Sort                   -- Sorts
    | Unknown                         -- for untyped variables

  -- Type Constructor
  TCons : Type
  TCons = TVariable

  -- Data Constructor
  DCons : Type
  DCons = TVariable

  -- type constructor argument
  TCA : Type
  TCA = TVariable
  -- data constructor argument
  DCA : Type
  DCA = TVariable


  -- Case Alternative
  data Alt = MKAlt TCons (List TCA) (List DCA) Expr
    --deriving (Show,Eq)

-- Data Type Declaration
data TDeclaration = TDecl TCons (List DCons)
  -- deriving (Show,Eq)

-- Value Declaration
data VDeclaration = VDecl TVariable Expr
  -- deriving (Show,Eq)

-- The Program
data Program = Prog (List TDeclaration) (List VDeclaration)
  -- deriving (Show,Eq)
