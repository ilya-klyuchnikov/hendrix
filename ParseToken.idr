module ParseToken

import Parser
import ParseError
import StdTokenDef
import TokenDef

%default total
%access public export

-- Text-Parser-Token copied here (almost fully)

-----------------------------------------------------------
-- White space & symbols
-----------------------------------------------------------

oneLineComment : Parser ()
oneLineComment =
    do{ try (string' (commentLine tokenDef))
      ; skipMany (satisfy (/= '\n'))
      ; pure ()
      }

inCommentSingle : Parser ()
inCommentSingle
    =   do { try (string' (commentEnd tokenDef)) ; pure () }
    <|> do { skipMany1 (noneOf startEnd)         ; assert_total inCommentSingle }
    <|> do { oneOf startEnd                      ; assert_total inCommentSingle }
    <?> "end of comment"
    where
      startEnd : List Char
      startEnd = nub (cast (commentEnd tokenDef ++ commentStart tokenDef))

mutual
  inCommentMulti : Parser ()
  inCommentMulti
      =   do { try (string' (commentEnd tokenDef))  ; pure () }
      <|> do { multiLineComment                     ; assert_total inCommentMulti }
      <|> do { skipMany1 (noneOf startEnd)          ; assert_total inCommentMulti }
      <|> do { oneOf startEnd                       ; assert_total inCommentMulti }
      <?> "end of comment"
      where
        startEnd : List Char
        startEnd = nub (cast (commentEnd tokenDef ++ commentStart tokenDef))

  inComment : Parser ()
  inComment = if nestedComments tokenDef
                then assert_total inCommentMulti
                else inCommentSingle

  multiLineComment : Parser ()
  multiLineComment =
      do { try (string' (commentStart tokenDef))
         ; inComment
         }

simpleSpace : Parser ()
simpleSpace = skipMany1 (satisfy isSpace)

noLine : Bool
noLine  = isEmptyString (commentLine tokenDef)
noMulti : Bool
noMulti = isEmptyString (commentStart tokenDef)

whiteSpace : Parser ()
whiteSpace with (noLine, noMulti)
  whiteSpace | (True,  True)  = skipMany (simpleSpace <?> "")
  whiteSpace | (True,  False) = skipMany (simpleSpace <|> multiLineComment <?> "")
  whiteSpace | (False, True)  = skipMany (simpleSpace <|> oneLineComment <?> "")
  whiteSpace | (False, False) = skipMany (simpleSpace <|> oneLineComment <|> multiLineComment <?> "")

lexeme : Parser b -> Parser b
lexeme p = do { x <- p; whiteSpace; pure x }

symbol : String -> Parser (List Char)
symbol name = lexeme (string' name)

-----------------------------------------------------------
-- Identifiers & Reserved words
-----------------------------------------------------------

theReservedNames : List String
theReservedNames = let sortedNames = sort (reservedNames tokenDef)
                   in
                   if caseSensitive tokenDef then sortedNames else map toLower sortedNames

isReserved : List String -> String -> Bool
isReserved names name = name `elem` names

isReservedName : String -> Bool
isReservedName name = isReserved theReservedNames caseName
    where
      caseName = if caseSensitive tokenDef then name else toLower name

ident : Parser (List Char)
ident
    = do{ c <- identStart tokenDef
        ; cs <- many (identLetter tokenDef)
        ; pure (c :: cs)
        }
    <?> "identifier"

identifier : Parser (List Char)
identifier =
    lexeme $ try $
    do { name <- ident
       ; if (isReservedName (cast name))
         then unexpected ("reserved word " ++ show name)
         else pure name
       }

caseString : List Char -> Parser (List Char)
caseString name =
    if caseSensitive tokenDef then string name
    else do { walk name; pure name } where
      caseChar    : Char -> Parser Char
      caseChar c  = if isAlpha c
                    then char (toLower c) <|> char (toUpper c)
                    else char c

      msg         : String
      msg         = show name

      walk : List Char -> Parser ()
      walk []        = pure ()
      walk (c :: cs) = do { (caseChar c) <?> msg; walk cs }

reserved : List Char -> Parser ()
reserved name =
    lexeme $ try $
    do { caseString name
       ; notFollowedBy (identLetter tokenDef) <?> ("end of " ++ show name)
       }

-----------------------------------------------------------
-- Operators & reserved ops
-----------------------------------------------------------

isReservedOp : String -> Bool
isReservedOp name =
    isReserved (sort (reservedOpNames tokenDef)) name

oper : Parser (List Char)
oper =
    do { c <- (opStart tokenDef)
       ; cs <- many (opLetter tokenDef)
       ; pure (c :: cs)
       }
     <?> "operator"

operator : Parser (List Char)
operator =
    lexeme $ try $
    do { name <- oper
       ; if (isReservedOp (cast name))
          then unexpected ("reserved operator " ++ show name)
          else pure name
       }

reservedOp : String -> Parser ()
reservedOp name =
    lexeme $ try $
    do { string' name
       ; notFollowedBy (opLetter tokenDef) <?> ("end of " ++ show name)
       }

-----------------------------------------------------------
-- Numbers
-----------------------------------------------------------

digits : List Char
digits = cast {to = List Char} "0123456789abcde"

digitToInt : Char -> Int
digitToInt c with (elemIndex c digits)
  digitToInt c | Just i = toIntNat i
  digitToInt c | Nothing = idris_crash "error"

number : Int -> Parser Char -> Parser Int
number base baseDigit
    = do { digits <- many1 baseDigit
         ; pure (foldl (\x, d => base * x + (digitToInt d)) 0 digits)
         }


decimal         : Parser Int
decimal         = number 10 digit
hexadecimal     : Parser Int
hexadecimal     = do { oneOf ['x', 'X']; number 16 hexDigit }
octal           : Parser Int
octal           = do { oneOf ['o', 'O']; number 8 octDigit  }

zeroNumber      : Parser Int
zeroNumber      = do { char '0'
                     ; hexadecimal <|> octal <|> decimal <|> pure 0 }
                  <?> ""

nat             : Parser Int
nat             = zeroNumber <|> decimal

sign            : Parser (Int -> Int)
sign            =   (char '-' *> pure negate)
                <|> (char '+' *> pure id)
                <|> pure id

int             : Parser Int
int             = do { f <- lexeme sign
                     ; n <- nat
                     ; pure (f n)
                     }

natural         : Parser Int
natural         = lexeme nat        <?> "natural"
