module Parser

import ParseError

%default total
%access public export

Source : Type
Source = String

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
