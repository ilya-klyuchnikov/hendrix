module ParseError

%default total
%access public export

-----------------------------------------------------------
-- Source Positions
-----------------------------------------------------------

SourceName     : Type
SourceName     = String

Line           : Type
Line           = Int

Column         : Type
Column         = Int

data SourcePosition = SourcePos SourceName Line Column

newPos : SourceName -> Line -> Column -> SourcePosition
newPos sourceName line column = SourcePos sourceName line column

initialPos : SourceName -> SourcePosition
initialPos sourceName = newPos sourceName 1 1

sourceName : SourcePosition -> SourceName
sourceName (SourcePos name line column) = name

sourceLine : SourcePosition -> Line
sourceLine (SourcePos name line column) = line

sourceColumn : SourcePosition -> Column
sourceColumn (SourcePos name line column) = column

updatePos : SourcePosition -> Char -> SourcePosition
updatePos (SourcePos name line column) '\n' = SourcePos name (line+1) 1
updatePos pos                          '\r' = pos
updatePos (SourcePos name line column)  _   = SourcePos name line (column + 1)

updatePosChars : SourcePosition -> List Char -> SourcePosition
updatePosChars = foldl updatePos

isEmptyString : String -> Bool
isEmptyString s = (length s) == 0

updatePosString : SourcePosition -> String -> SourcePosition
updatePosString pos string = updatePosChars pos (cast string)

Show SourcePosition where
  show (SourcePos name line column) =
    if isEmptyString name then showLineColumn else "\"" ++ name ++ "\" " ++ showLineColumn where
      showLineColumn = "(line " ++ show line ++ ", column " ++ show column ++ ")"

-----------------------------------------------------------
-- Messages
-----------------------------------------------------------
data Message        = SysUnExpect String   --library generated unexpect
                    | UnExpect    String   --unexpected something
                    | Expect      String   --expecting something
                    | Msg         String   --raw message

messageToEnum : Message -> Nat
messageToEnum (SysUnExpect _) = 0
messageToEnum (UnExpect _)    = 1
messageToEnum (Expect _)      = 2
messageToEnum (Msg _)         = 2

messageCompare : Message -> Message -> Ordering
messageCompare msg1 msg2 = compare (messageToEnum msg1) (messageToEnum msg2)

messageString : Message -> String
messageString (SysUnExpect s) = s
messageString (UnExpect s)    = s
messageString (Expect s)      = s
messageString (Msg s)         = s

messageEq : Message -> Message -> Bool
messageEq msg1 msg2 = (messageCompare msg1 msg2 == EQ)

-----------------------------------------------------------
-- Parse Errors
-----------------------------------------------------------

data ParseError = PError SourcePosition (List Message)

errorPos : ParseError -> SourcePosition
errorPos (PError pos msgs) = pos

errorMessages : ParseError -> (List Message)
errorMessages (PError pos msgs) = sortBy messageCompare msgs

errorIsUnknown : ParseError -> Bool
errorIsUnknown (PError pos msgs) = isNil msgs

-----------------------------------------------------------
-- Create parse errors
-----------------------------------------------------------
newErrorUnknown : SourcePosition -> ParseError
newErrorUnknown pos = PError pos []

newErrorMessage : Message -> SourcePosition -> ParseError
newErrorMessage msg pos = PError pos [msg]

addErrorMessage : Message -> ParseError -> ParseError
addErrorMessage msg (PError pos msgs) = PError pos (msg :: msgs)

setErrorPos : SourcePosition -> ParseError -> ParseError
setErrorPos pos (PError _ msgs) = PError pos msgs

setErrorMessage : Message -> ParseError -> ParseError
setErrorMessage msg (PError pos msgs) = PError pos (msg :: (filter (not . messageEq msg) msgs))

mergeError : ParseError -> ParseError -> ParseError
mergeError (PError _ msgs1) (PError pos msgs2) = PError pos (msgs1 ++ msgs2)

-----------------------------------------------------------
-- Show Parse Errors
-----------------------------------------------------------

showErrorMessages : String -> String -> String -> String -> String -> (List Message) -> String
showErrorMessages msgOr msgUnknown msgExpecting msgUnExpected msgEndOfInput msgs =
  if isNil msgs then msgUnknown else concat $ map ("\n" ++) $ clean $ orderedMessages
    where
      clean : List String -> List String
      clean = nub . filter (not . isEmptyString)

      seperate : String -> List String -> String
      seperate sep []   = ""
      seperate sep [m]  = m
      seperate sep (m :: ms) = m ++ sep ++ seperate sep ms

      commaSep : List String -> String
      commaSep = seperate ", " . clean
      semiSep  : List String -> String
      semiSep  = seperate "; " . clean

      commasOr           : List String -> String
      commasOr []        = ""
      commasOr [m]       = m
      commasOr (m :: ms) = commaSep (init (m :: ms)) ++ " " ++ msgOr ++ " " ++ last (m :: ms)

      showMany : String -> List Message -> String
      showMany pre msgs = case (clean (map messageString msgs)) of
                            [] => ""
                            ms => if isEmptyString pre then commasOr ms else pre ++ " " ++ (commasOr ms)

      showExpect : List Message -> String
      showExpect = showMany msgExpecting

      showUnExpect : List Message -> String
      showUnExpect = showMany msgUnExpected

      showMessages : List Message -> String
      showMessages = showMany ""

      showSysUnExpect : List Message -> List Message -> String
      -- showSysUnExpect sysUnExpectMsgs unExpectMsgs
      showSysUnExpect _ (_ :: _) = ""
      showSysUnExpect [] _ = ""
      showSysUnExpect (first :: _) _ =
        let firstMsg = messageString (first) in
        if isEmptyString firstMsg
          then seperate " " [msgUnExpected, msgEndOfInput]
          else seperate " " [msgUnExpected, firstMsg]

      orderedMessages : List String
      orderedMessages = let (sysUnExpect,msgs1)   = span (messageEq (SysUnExpect "")) msgs
                            (unExpect,msgs2)      = span (messageEq (UnExpect "")) msgs1
                            (expect,messages)     = span (messageEq (Expect "")) msgs2
                        in  [showSysUnExpect sysUnExpect unExpect,
                             showUnExpect unExpect,
                             showExpect expect,
                             showMessages messages]

Show ParseError where
  show err
    = show (errorPos err) ++ ":" ++
      showErrorMessages "or" "unknown parse error" "expecting" "unexpected" "end of input" (errorMessages err)
