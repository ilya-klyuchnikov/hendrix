module Parser

import ParseError

%default total
%access public export

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
  -- alternative via functora
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

updateState : (State -> State) -> Parser State
updateState f
    = PT (\state => Empty (Ok state (f state) (unknownError state)))

unexpected : String -> Parser a
unexpected msg
    = PT (\state => Empty (Error (newErrorMessage (UnExpect msg) (statePos state))))


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
