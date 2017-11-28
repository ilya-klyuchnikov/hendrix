module StdTokenDef

import Parser
import StdTokenDef

%default total
%access public export

henk : TokenDefinition
henk  = record
          { commentStart    = "{-"
          , commentEnd      = "-}"
          , commentLine     = "--"
          , nestedComments  = True
          , identStart      = letter
          , identLetter     = alphaNum <|> oneOf (cast "_'")
          , opStart         = oneOf (cast ":=\\->/|~.*[]")
          , opLetter        = oneOf (cast ":=\\->/|~.*[]")
          , reservedOpNames = ["::","=","\\","->","=>","/\\","\\/" ,"|~|",".",":","*","[]"]
          , reservedNames   = [ "case", "data", "letrec", "type", "import", "in", "let", "of", "at", "Int"]
          , caseSensitive   = True
          } emptyStyle

tokenDef : TokenDefinition
tokenDef = henk
