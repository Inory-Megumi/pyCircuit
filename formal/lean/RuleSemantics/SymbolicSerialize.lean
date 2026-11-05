import RuleSemantics.Symbolic

/-!
Verification-only serialization of actual closed Rule definitions. Preflight
runs before symbolic construction; complete JSON is returned only on success.
Output coverage and RTL port/state relations belong to the independent encoder.
-/

namespace RuleSemantics.SymbolicSerialize

open Syntax Symbolic

private def maxWork : Nat := 100000
private def maxBytes : Nat := 8 * 1024 * 1024
private def maxDepth : Nat := 256

private structure Budget where
  work : Nat := 0
  visits : Nat := 0
  bytes : Nat := 0
  text : String := ""

private abbrev Build := StateT Budget (Except String)

private def pay (amount : Nat := 1) : Build Unit := do
  let budget ← get
  if amount > maxWork - budget.work then
    throw "symbolic construction exceeds 100000 work units"
  set { budget with work := budget.work + amount }

private def checkDepth (depth : Nat) : Build Unit := do
  if depth > maxDepth then throw "symbolic syntax/term depth exceeds 256"

private def checkType : ValueType → Build Unit
  | .bool => pure ()
  | .bits width => do
    if width = 0 then throw "hardware formula requires positive bit widths"

private def checkExpr (expression : Expr signature type) (depth : Nat) : Build Unit := do
  checkDepth depth
  pay
  checkType type
  match (dependent := true) (generalizing := true) expression with
  | .boolLit _ | .bitsLit _ | .input _ | .reg _ => pure ()
  | .add left right | .sub left right | .ult left right | .eq left right | .and left right =>
    checkExpr left (depth + 1)
    checkExpr right (depth + 1)
  | .not value => checkExpr value (depth + 1)
  | .bit value => checkExpr value (depth + 1)
  | .concat high low =>
    checkExpr high (depth + 1)
    checkExpr low (depth + 1)
  | .ite condition yes no =>
    checkExpr condition (depth + 1)
    checkExpr yes (depth + 1)
    checkExpr no (depth + 1)

private def checkCommand (command : Command signature) (depth : Nat) : Build Unit := do
  checkDepth depth
  pay
  match command with
  | .skip => pure ()
  | .assign _ value =>
    pay signature.nr
    checkExpr value (depth + 1)
  | .require condition => checkExpr condition (depth + 1)
  | .seq first second =>
    checkCommand first (depth + 1)
    checkCommand second (depth + 1)

private def countNames (names : List String) : Build Nat := do
  let mut count := 0
  for name in names do
    pay
    if name.utf8ByteSize > maxBytes then throw "metadata name exceeds 8 MiB"
    count := count + 1
  return count

private def preflight (signature : Signature) (rules : List (RuleDef signature))
    (definitionName : String) (inputNames registerNames registerKeys outputNames : List String)
    (outputExpressions : List (Output signature)) : Build Unit := do
  if signature.nr > 64 || signature.ni > 64 then
    throw "hardware formula supports at most 64 registers and 64 inputs"
  pay (1 + 2 * signature.nr)
  let _ ← countNames [definitionName]
  for index in List.finRange signature.ni do
    checkType (signature.inputType index)
  for register in List.finRange signature.nr do
    checkType (.bits (signature.regWidth register))
  if (← countNames inputNames) != signature.ni then throw "input name count differs from signature"
  if (← countNames registerNames) != signature.nr then throw "register name count differs from signature"
  if (← countNames registerKeys) != signature.nr then throw "register owner count differs from signature"
  let outputCount ← countNames outputNames
  let mut registerCount := 0
  for output in outputExpressions do
    pay
    checkType (.bits output.width)
    checkExpr output.expression 1
    registerCount := registerCount + 1
  if outputCount != registerCount then throw "output name/expression counts differ"
  for rule in rules do
    pay (1 + signature.nr)
    checkExpr rule.guard 1
    checkCommand rule.body 1

private def append (piece : String) : Build Unit := do
  let budget ← get
  let bytes := piece.utf8ByteSize
  if bytes > maxBytes - budget.bytes then throw "formula JSON exceeds 8 MiB"
  set { budget with bytes := budget.bytes + bytes, text := budget.text ++ piece }

private def quoted (value : String) : Build Unit := do
  append "\""
  for character in value do
    if character = '"' then append "\\\""
    else if character = '\\' then append "\\\\"
    else if character = '\n' then append "\\n"
    else if character = '\r' then append "\\r"
    else if character = '\t' then append "\\t"
    else if character.toNat < 32 then
      append ("\\u00" |>.push (Nat.digitChar (character.toNat / 16))
        |>.push (Nat.digitChar (character.toNat % 16)))
    else append (String.singleton character)
  append "\""

private def number (value : Nat) : Build Unit := do
  -- Refuse enormous numeral conversion before allocating its decimal text.
  -- A binary length of 3*maxBytes already requires over 0.9*maxBytes decimal
  -- digits; this conservative cap bounds conversion storage independently.
  if value.log2 > 3 * maxBytes then throw "formula numeral exceeds conversion budget"
  append (toString value)

private def decimal (value : Nat) : Build Unit := do
  append "\""
  number value
  append "\""

private def emitType (type : ValueType) : Build Unit := do
  checkType type
  match type with
  | .bool => append "{\"kind\":\"bool\"}"
  | .bits width =>
    append "{\"kind\":\"bits\",\"width\":"
    number width
    append "}"

private def startTerm (op : String) (type : ValueType) : Build Unit := do
  append "{\"op\":"
  quoted op
  append ",\"type\":"
  emitType type

private def visit (depth : Nat) : Build Unit := do
  checkDepth depth
  let budget ← get
  if budget.visits ≥ maxWork then throw "formula expansion exceeds 100000 term visits"
  set { budget with visits := budget.visits + 1 }

private def emitTerm (term : Term signature type) (depth : Nat) : Build Unit := do
  visit depth
  match (dependent := true) (generalizing := true) term with
  | .boolLit value =>
    startTerm "boolLit" type
    append ",\"value\":"
    append (if value then "true" else "false")
  | .bitsLit value =>
    startTerm "bitsLit" type
    append ",\"value\":"
    decimal value.toNat
  | .input index =>
    startTerm "input" type
    append ",\"index\":"
    number index.val
  | .read register =>
    startTerm "read" type
    append ",\"index\":"
    number register.val
  | .add left right =>
    startTerm "add" type
    append ",\"args\":["
    emitTerm left (depth + 1)
    append ","
    emitTerm right (depth + 1)
    append "]"
  | .sub left right =>
    startTerm "sub" type
    append ",\"args\":["
    emitTerm left (depth + 1)
    append ","
    emitTerm right (depth + 1)
    append "]"
  | .ult left right =>
    startTerm "ult" type
    append ",\"args\":["
    emitTerm left (depth + 1)
    append ","
    emitTerm right (depth + 1)
    append "]"
  | .eq left right =>
    startTerm "eq" type
    append ",\"args\":["
    emitTerm left (depth + 1)
    append ","
    emitTerm right (depth + 1)
    append "]"
  | .and left right =>
    startTerm "and" type
    append ",\"args\":["
    emitTerm left (depth + 1)
    append ","
    emitTerm right (depth + 1)
    append "]"
  | .not value =>
    startTerm "not" type
    append ",\"args\":["
    emitTerm value (depth + 1)
    append "]"
  | .ite condition yes no =>
    startTerm "ite" type
    append ",\"args\":["
    emitTerm condition (depth + 1)
    append ","
    emitTerm yes (depth + 1)
    append ","
    emitTerm no (depth + 1)
    append "]"
  | .bit value =>
    startTerm "bit" type
    append ",\"args\":["
    emitTerm value (depth + 1)
    append "]"
  | .concat high low =>
    startTerm "concat" type
    append ",\"args\":["
    emitTerm high (depth + 1)
    append ","
    emitTerm low (depth + 1)
    append "]"
  append "}"

private def emitModel (signature : Signature) (initialState : State signature)
    (definitionName : String) (inputNames registerNames registerKeys outputNames : List String)
    (outputExpressions : List (Output signature)) (bank : Bank signature) : Build Unit := do
  append "{\"schema\":\"pycircuit-rule-transition-v2\",\"definition\":"
  quoted definitionName
  append ",\"inputs\":["
  for index in List.finRange signature.ni do
    if index.val != 0 then append ","
    append "{\"name\":"
    quoted (inputNames[index.val]!)
    append ",\"type\":"
    emitType (signature.inputType index)
    append "}"
  append "],\"registers\":["
  for register in List.finRange signature.nr do
    if register.val != 0 then append ","
    append "{\"name\":"
    quoted (registerNames[register.val]!)
    append ",\"owner\":"
    quoted (registerKeys[register.val]!)
    append ",\"width\":"
    number (signature.regWidth register)
    append ",\"initial\":"
    decimal (initialState register).toNat
    append "}"
  append "],\"outputs\":["
  let mut first := true
  let entryBank := cacheBank (fun register => Term.read register)
  for (name, output) in outputNames.zip outputExpressions do
    if !first then append ","
    first := false
    append "{\"name\":"
    quoted name
    append ",\"type\":"
    emitType (.bits output.width)
    append ",\"term\":"
    emitTerm (lowerExpr output.expression entryBank) 1
    append "}"
  append "],\"next\":["
  for register in List.finRange signature.nr do
    if register.val != 0 then append ","
    emitTerm (bank.get register) 1
  append "]}"

/-- Serialize actual closed definitions, returning complete JSON or a diagnostic. -/
def serialize (signature : Signature) (rules : List (RuleDef signature))
    (initialState : State signature) (definitionName : String)
    (inputNames registerNames registerKeys outputNames : List String)
    (outputExpressions : List (Output signature)) : Except String String := do
  let (_, checked) ← (preflight signature rules definitionName inputNames registerNames registerKeys
    outputNames outputExpressions).run {}
  -- This let is reached only after complete preflight succeeds.
  let bank := nextState rules
  let (_, rendered) ← (emitModel signature initialState definitionName inputNames registerNames registerKeys
    outputNames outputExpressions bank).run checked
  return rendered.text

end RuleSemantics.SymbolicSerialize
