module Parser

import ParseError

%default total
%access export

infixl  0 <?>

Source : Type
Source = List Char

record State where
  constructor ST
  stateInput : Source
  statePos   : SourcePosition

data Reply a = Ok a State ParseError     --parsing succeeded with @a@
             | Error ParseError          --parsing failed

Functor Reply where
  map f (Ok x state err) = Ok (f x) state err
  map f (Error err) = (Error err)

data Processed a = Consumed a            --input is consumed
                 | Empty a               --no input is consumed

Functor Processed where
  map f (Consumed x) = Consumed (f x)
  map f (Empty x)    = Empty (f x)

data Parser a = PT (State -> Processed (Reply a))

setExpectError : String -> ParseError -> ParseError
setExpectError msg err   = setErrorMessage (Expect msg) err
sysUnExpectError : String -> SourcePosition -> Reply a
sysUnExpectError msg pos = Error (newErrorMessage (SysUnExpect msg) pos)
unknownError : State -> ParseError
unknownError state       = newErrorUnknown (statePos state)

runP : Parser a -> State -> Processed (Reply a)
runP (PT p) = p

parserReply : Processed a -> a
parserReply (Consumed reply) = reply
parserReply (Empty reply)    = reply

parse : Parser a -> SourceName -> Source -> Either ParseError a
parse p name input
    = case parserReply (runP p (ST input (initialPos name))) of
        Ok x _ _    => Right x
        Error err   => Left err

Functor Parser where
  map f (PT p)
    = PT (\ state =>
        case (p state) of
          Consumed reply => Consumed (mapReply reply)
          Empty    reply => Empty    (mapReply reply)
      )
    where
      mapReply : Reply a -> Reply b
      mapReply reply
        = case reply of
            Ok x state err => Ok (f x) state err
            Error err      => Error err
  -- alternative via functors
  -- map f (PT p) = PT (map (map f) . p)


mergeErrorReply : ParseError -> Reply a -> Reply a
mergeErrorReply err1 reply
  = case reply of
      Ok x state err2 => Ok x state (mergeError err1 err2)
      Error err2      => Error (mergeError err1 err2)

Applicative Parser where
  pure x
    = PT (\state => Empty (Ok x state (unknownError state)))
  (PT f) <*> (PT a)
    = PT (\state => case (f state) of
        Consumed (Ok g state1 err1) =>
          case (a state1) of
              Consumed (Ok b state2 err2) => Consumed (Ok (g b) state2 err2)
              Empty    (Ok b state2 err2) => Consumed (Ok (g b) state2 (mergeError err1 err2))
              Consumed (Error err2)       => Consumed (Error err2)
              Empty    (Error err2)       => Consumed (Error (mergeError err1 err2))
        Empty    (Ok g state1 err1) =>
          case (a state1) of
              Consumed (Ok b state2 err2) => Consumed (Ok (g b) state2 err2)
              Empty    (Ok b state2 err2) => Empty    (Ok (g b) state2 (mergeError err1 err2))
              Consumed (Error err2)       => Consumed (Error err2)
              Empty    (Error err2)       => Consumed (Error (mergeError err1 err2))
        Consumed (Error err1)       => Consumed (Error err1)
        Empty    (Error err1)       => Empty    (Error err1)
      )

-- Applicative f => f (a -> b) -> f a -> f b
infixl 2 <*>|
(<*>|) : Parser (a -> b) -> Lazy (Parser a) -> Parser b
(PT f) <*>| a
  = PT (\state => case (f state) of
    Consumed (Ok g state1 err1) =>
      let (PT a') = a in
      case (a' state1) of
          Consumed (Ok b state2 err2) => Consumed (Ok (g b) state2 err2)
          Empty    (Ok b state2 err2) => Consumed (Ok (g b) state2 (mergeError err1 err2))
          Consumed (Error err2)       => Consumed (Error err2)
          Empty    (Error err2)       => Consumed (Error (mergeError err1 err2))
    Empty    (Ok g state1 err1) =>
      let (PT a') = a in
      case (a' state1) of
          Consumed (Ok b state2 err2) => Consumed (Ok (g b) state2 err2)
          Empty    (Ok b state2 err2) => Empty    (Ok (g b) state2 (mergeError err1 err2))
          Consumed (Error err2)       => Consumed (Error err2)
          Empty    (Error err2)       => Consumed (Error (mergeError err1 err2))
    Consumed (Error err1)       => Consumed (Error err1)
    Empty    (Error err1)       => Empty    (Error err1)
  )

Monad Parser where
  (PT p) >>= next
    = PT (\state => case (p state) of
        Consumed (Ok x state1 err1) =>
          case runP (next x) state1 of
            -- TODO - why not merge errors hre?
            Consumed reply2 => Consumed reply2
            Empty    reply2 => Consumed (mergeErrorReply err1 reply2)
        Empty    (Ok x state1 err1) =>
          case runP (next x) state1 of
            -- TODO - why not merge errors hre?
            Consumed reply2 => Consumed reply2
            Empty    reply2 => Empty (mergeErrorReply err1 reply2)
        Consumed (Error err1)       => Consumed (Error err1)
        Empty    (Error err1)       => Empty    (Error err1)
      )

Alternative Parser where
  empty
    = PT (\state => Empty (Error (unknownError state)))
  (PT p1) <|> (PT p2)
    = PT (\state =>
        case (p1 state) of
          Empty (Error err) => case (p2 state) of
                                 Empty reply => Empty (mergeErrorReply err reply)
                                 consumed    => consumed
          other             => other
      )

infixl 3 <|>|
(<|>|) : Parser a -> Lazy (Parser a) -> Parser a
(PT p1) <|>| p2
  = PT (\state =>
      case (p1 state) of
        Empty (Error err) => let (PT p2') = p2 in
                             case (p2' state) of
                               Empty reply => Empty (mergeErrorReply err reply)
                               consumed    => consumed
        other             => other
    )

----------

updateState : (State -> State) -> Parser State
updateState f
    = PT (\state => Empty (Ok state (f state) (unknownError state)))

getState : Parser State
getState = updateState id

setState : State -> Parser State
setState state = updateState (const state)

unexpected : String -> Parser a
unexpected msg
    = PT (\state => Empty (Error (newErrorMessage (UnExpect msg) (statePos state))))

getPosition : Parser SourcePosition
getPosition = do state <- getState; pure (statePos state)

getInput : Parser Source
getInput = do state <- getState; pure (stateInput state)

setPosition : SourcePosition -> Parser ()
setPosition pos = do updateState (\ s => ST (stateInput s) pos); pure ()

setInput : Source -> Parser ()
setInput input = do updateState (\ s => ST input (statePos s)); pure ()


-----------------------------------------------------------
-- Primitive Parsers:
--  try, satisfy, onFail, unexpected and updateState
-----------------------------------------------------------

try : Parser a -> Parser a
try (PT p)
    = PT (\ state =>
        case (p state) of
          Consumed (Error err)  => Empty (Error (setErrorPos (statePos state) err))
          Consumed ok           => Empty ok
          empty                 => empty
      )

token : Parser a -> Parser a
token p --obsolete, use "try" instead
    = try p


satisfy : (Char -> Bool) -> Parser Char
satisfy test
    = PT ( \ s => let pos = statePos s in
        case (stateInput s) of
          (c :: cs) => if test c
                       then let newpos = updatePos pos c
                                newstate = ST cs newpos
                            in Consumed (Ok c newstate (newErrorUnknown newpos))
                       else Empty (sysUnExpectError (show [c]) pos)
          []        => Empty (sysUnExpectError "" pos)
      )

onFail : Parser a -> String -> Parser a
onFail (PT p) msg
    = PT (\state =>
        case (p state) of
          Empty reply =>
            Empty $
               case reply of
                 Error err        => Error (setExpectError msg err)
                 Ok x state1 err  => if errorIsUnknown err
                                     then  reply
                                     else Ok x state1 (setExpectError msg err)
          other       => other
      )

-- TODO - remove and simplify
-- we can use other combinators for it

string : List Char -> Parser (List Char)
string str = PT walkAll where
  walkAll (ST input pos) = walk1 str input where
    ok : Source -> Reply (List Char)
    ok cs = let newpos = updatePosChars pos str
                newstate = ST cs newpos
            in (Ok str newstate (newErrorUnknown newpos))

    errEof : Reply (List Char)
    errEof = Error (setErrorMessage (Expect (show str)) (newErrorMessage (SysUnExpect "") pos))

    errExpect : Char -> Reply (List Char)
    errExpect c = Error (setErrorMessage (Expect (show str)) (newErrorMessage (SysUnExpect (show [c])) pos))    --

    walk : (List Char) -> Source -> Reply (List Char)
    walk [] cs                = ok cs
    walk xs []                = errEof
    walk (x :: xs) (c :: cs)  = if x == c then walk xs cs else errExpect c

    walk1 : (List Char) -> Source -> Processed (Reply (List Char))
    walk1 [] cs               = Empty (ok cs)
    walk1 xs []               = Empty (errEof)
    walk1 (x :: xs) (c :: cs) = if x == c then Consumed (walk xs cs) else Empty (errExpect c)

oneOf :  List Char -> Parser Char
oneOf cs  = satisfy (\c => c `elem` cs)

noneOf :  List Char -> Parser Char
noneOf cs  = satisfy (\c => not (c `elem` cs))

anySymbol : Parser Char
anySymbol = satisfy (const True)

choice : List (Parser a) -> Parser a
choice ps = foldr (<|>) empty ps

option : a -> Parser a -> Parser a
option x p = p <|> pure x

optional : Parser a -> Parser ()
optional p = do { p; pure () } <|> pure ()

between : Parser open -> Parser close -> Parser a -> Parser a
between op cl p = do op; x <- p; cl; pure x

-- infixr 3 :::
-- private
-- (:::) : a -> List a -> List a
-- (:::) x xs = x :: xs

many : Parser a -> Parser (List a)
many p = scan id where
  scan : (List a -> List a) -> Parser (List a)
  scan f = do {x <- p; assert_total (scan (\tail => f (x :: tail))) } <|> pure (f [])
-- many p = (try ((pure (:::) <*> p) <*>| many p)) <|> pure []

many1 : Parser a -> Parser (List a)
many1 p = do x <- p; xs <- many p; pure (x :: xs)

skipMany : Parser a -> Parser ()
skipMany p = do xs <- (many p); pure ()

skipMany1 : Parser a -> Parser ()
skipMany1 p = do x <- (many1 p); pure ()

sepBy1 : Parser a -> Parser sep -> Parser (List a)
sepBy1 p sep = do x <- p ; xs <- many (sep *> p); pure (x :: xs)

sepBy : Parser a -> Parser sep -> Parser (List a)
sepBy p sep = sepBy1 p sep <|> pure []

count : Nat -> Parser a -> Parser (List a)
count Z _ = pure []
count n p = sequence (take n (repeat p))

chainl1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op = do x <- p; rest x
  where
    rest : a -> Parser a
    rest x = do {f <- op; y <- p; (assert_total (rest (f x y)))} <|> pure x

chainr1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 p op = scan where
  mutual
    scan : Parser a
    scan = do x <- p; rest x
    rest : a -> Parser a
    rest x = do {f <- op; y <- (assert_total scan); pure (f x y)} <|> pure x

chainr : Parser a -> Parser (a -> a -> a) -> a-> Parser a
chainr p op x       = (chainr1 p op) <|> (pure x)
chainl : Parser a -> Parser (a -> a -> a) -> a-> Parser a
chainl p op x       = (chainl1 p op) <|> (pure x)

notFollowedBy : Parser Char -> Parser ()
notFollowedBy p = try (do { c <- p; unexpected (show [c]) } <|> pure ())

eof : Parser ()
eof = notFollowedBy anySymbol

manyTill : Parser a -> Parser end -> Parser (List a)
manyTill p end = scan where
  scan : Parser (List a)
  scan = do { end; pure [] } <|> do { x <- p; xs <- (assert_total scan); pure (x :: xs) }

lookAhead : Parser a -> Parser a
lookAhead p = do state <- getState
                 x <- p
                 setState state
                 pure x

char : Char -> Parser Char
char c = satisfy (c ==)

space : Parser Char
space = satisfy isSpace

newline : Parser Char
newline = char '\n'

upper : Parser Char
upper = satisfy isUpper

lower : Parser Char
lower = satisfy isLower

alphaNum : Parser Char
alphaNum = satisfy isAlphaNum

letter : Parser Char
letter = satisfy isAlpha

digit : Parser Char
digit = satisfy isDigit

hexDigit : Parser Char
hexDigit = satisfy isHexDigit

octDigit : Parser Char
octDigit = satisfy isOctDigit

---- Testing
testString1 : parse (string ['a', 'b']) "my_source" ['a', 'b', 'c'] = Right ['a', 'b']
testString1 = Refl

testString2 : parse (string ['a']) "my_source" [] = Left (PError (SourcePos "my_source" 1 1) [Expect "['a']", SysUnExpect ""])
testString2 = Refl

testString3 : parse (string ['a', 'b']) "my_source" ['a', 'c'] = Left (PError (SourcePos "my_source" 1 1) [Expect "['a', 'b']", SysUnExpect "['c']"])
testString3 = Refl

testBind : parse ( (string ['a', 'b']) >>= \x => (string ['c', 'd']))  "my_source" ['a', 'b', 'c', 'd'] = Right ['c', 'd']
testBind = Refl

testBindAndPure : parse ( (string ['a', 'b']) >>= \x => (string ['c', 'd']) >>= \y => pure (x ++ y))  "my_source" ['a', 'b', 'c', 'd'] = Right ['a', 'b', 'c', 'd']
testBindAndPure = Refl
