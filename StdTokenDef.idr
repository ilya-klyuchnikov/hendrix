module StdTokenDef

import Parser

%default total
%access public export

record TokenDefinition where
  constructor TokenDef
  commentStart   : String
  commentEnd     : String
  commentLine    : String
  nestedComments : Bool
  identStart     : Parser Char
  identLetter    : Parser Char
  opStart        : Parser Char
  opLetter       : Parser Char
  reservedNames  : List String
  reservedOpNames: List String
  caseSensitive  : Bool

emptyStyle : TokenDefinition
emptyStyle = TokenDef
                { commentStart   = "" }
                { commentEnd     = "" }
                { commentLine    = "" }
                { nestedComments = True }
                { identStart     = unexpected "identifier" }
                { identLetter    = unexpected "identifier" }
                { opStart        = unexpected "operator" }
                { opLetter       = unexpected "operator" }
                { reservedOpNames= [] }
                { reservedNames  = [] }
                { caseSensitive  = True }
                           ;
haskellStyle : TokenDefinition
haskellStyle = record
                { commentStart   = "{-"
                , commentEnd     = "-}"
                , commentLine    = "--"
                , nestedComments = True
                , identStart     = letter
                , identLetter   = alphaNum <|> oneOf (cast "_'")
                , opStart   = oneOf (cast ":!#$%&*+./<=>?@\\^|-~")
                , opLetter   = oneOf (cast ":!#$%&*+./<=>?@\\^|-~")
                , reservedOpNames= []
                , reservedNames  = []
                , caseSensitive  = True
                } emptyStyle

javaStyle   : TokenDefinition
javaStyle   = record
                { commentStart   = "/*"
                , commentEnd   = "*/"
                , commentLine   = "//"
                , nestedComments = True
                , identStart   = letter
                , identLetter   = alphaNum <|> oneOf (cast "_'")
                -- fixed set of operators: use 'symbol'
                , reservedNames  = []
                , reservedOpNames= []
                , caseSensitive  = False
                } emptyStyle

haskell     : TokenDefinition
haskell     = record
                { reservedOpNames= ["::","..","=","\\","|","<-","->","@","~","=>"]
                , reservedNames  = ["let","in","case","of","if","then","else",
                                    "data","type",
                                    "class","default","deriving","do","import",
                                    "infix","infixl","infixr","instance","module",
                                    "newtype","where",
                                    "primitive"]
                } haskellStyle

mondrian    : TokenDefinition
mondrian    = record
                { reservedNames = [ "case", "class", "default", "extends"
                                  , "import", "in", "let", "new", "of", "package"]
                , caseSensitive  = True
                } javaStyle
