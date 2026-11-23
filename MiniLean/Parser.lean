import Lean
import MiniLean.Pretty

/-!
# MiniLean.Parser

Position-aware lexer and recursive-descent parsers for formulas and proof terms.
-/

namespace MiniLean

structure Position where
  line : Nat
  column : Nat
  deriving Repr, DecidableEq, Inhabited

structure Token where
  text : String
  position : Position
  deriving Repr, DecidableEq, Inhabited

structure ParseError where
  message : String
  position : Position
  deriving Repr, DecidableEq, Inhabited

private def advance (pos : Position) (c : Char) : Position :=
  if c == '\n' then ⟨pos.line + 1, 1⟩ else ⟨pos.line, pos.column + 1⟩

private def isWord (c : Char) : Bool := c.isAlphanum || c == '_'

private def isSymbolChar (c : Char) : Bool :=
  "()[],;=→∧∨⊥".contains c || c == '-' || c == '>'

private partial def lexLoop : List Char → Position → Except ParseError (List Token)
  | [], _ => .ok []
  | c :: cs, pos =>
      if c.isWhitespace then lexLoop cs (advance pos c)
      else if isWord c then
        let word := (c :: cs).takeWhile isWord
        let rest := (c :: cs).drop word.length
        let token := ⟨String.mk word, pos⟩
        let endPos := word.foldl advance pos
        match lexLoop rest endPos with
        | .ok tokens => .ok (token :: tokens)
        | .error err => .error err
      else if isSymbolChar c then
        let (symbol, rest, width) :=
          if c == '-' && cs.head? == some '>' then ("->", cs.drop 1, 2)
          else (String.singleton c, cs, 1)
        match lexLoop rest ⟨pos.line, pos.column + width⟩ with
        | .ok tokens => .ok (⟨symbol, pos⟩ :: tokens)
        | .error err => .error err
      else .error ⟨s!"Unexpected character '{c}'", pos⟩

/-- Tokenize source and retain each token's one-based starting position. -/
def lex (source : String) : Except ParseError (List Token) :=
  lexLoop source.toList ⟨1, 1⟩

private abbrev Parser := StateT (List Token) (Except ParseError)

private def withEndOfInput (source : String) (tokens : List Token) : List Token :=
  let endPosition := source.toList.foldl advance ⟨1, 1⟩
  tokens ++ [⟨"<eof>", endPosition⟩]

private def consumedInput (tokens : List Token) : Bool :=
  match tokens with
  | [] => true
  | [token] => token.text == "<eof>"
  | _ => false

private instance : Inhabited (Parser Proof) :=
  ⟨fun _ => .error ⟨"unreachable", ⟨1, 1⟩⟩⟩

private def fail (message : String) : Parser α := do
  let tokens ← get
  let position := (tokens.head?).map Token.position |>.getD ⟨1, 1⟩
  throw ⟨message, position⟩

private def takeToken (expected : String) : Parser Unit := do
  let tokens ← get
  match tokens with
  | token :: rest =>
      if token.text == "<eof>" then throw ⟨s!"Expected '{expected}', found end of input", token.position⟩
      else if token.text == expected then set rest
      else throw ⟨s!"Expected '{expected}', found '{token.text}'", token.position⟩
  | [] => throw ⟨s!"Expected '{expected}', found end of input", ⟨1, 1⟩⟩

private def takeName : Parser String := do
  let tokens ← get
  match tokens with
  | token :: rest =>
      if token.text == "<eof>" then throw ⟨"Expected a name, found end of input", token.position⟩
      else if token.text == "_" || (token.text.toList.head?.getD ' ').isAlpha then
        set rest
        pure token.text
      else throw ⟨s!"Expected a name, found '{token.text}'", token.position⟩
  | [] => throw ⟨"Expected a name, found end of input", ⟨1, 1⟩⟩

mutual
private partial def parseAtom : Parser Formula := do
  let tokens ← get
  match tokens with
  | token :: rest =>
      if token.text == "<eof>" then throw ⟨"Expected a formula, found end of input", token.position⟩
      else if token.text == "⊥" || token.text == "false" then
        set rest
        pure .falsum
      else if token.text.startsWith "P" then
        match (token.text.drop 1).toNat? with
        | some n => set rest; pure (.atom n)
        | none => throw ⟨s!"Expected an atom such as P0, found '{token.text}'", token.position⟩
      else if token.text == "(" then
        set rest
        let formula ← parseFormulaTokens
        takeToken ")"
        pure formula
      else throw ⟨s!"Expected a formula, found '{token.text}'", token.position⟩
  | [] => fail "Expected a formula, found end of input"

private partial def parseConj : Parser Formula := do
  let left ← parseAtom
  parseConjTail left

private partial def parseConjTail (left : Formula) : Parser Formula := do
  let tokens ← get
  match tokens with
  | op :: rest =>
      if op.text == "∧" then
        set rest
        let right ← parseAtom
        parseConjTail (.and left right)
      else pure left
  | [] => pure left

private partial def parseDisj : Parser Formula := do
  let left ← parseConj
  parseDisjTail left

private partial def parseDisjTail (left : Formula) : Parser Formula := do
  let tokens ← get
  match tokens with
  | op :: rest =>
      if op.text == "∨" then
        set rest
        let right ← parseConj
        parseDisjTail (.or left right)
      else pure left
  | [] => pure left

private partial def parseFormulaTokens : Parser Formula := do
  let left ← parseDisj
  let tokens ← get
  match tokens with
  | op :: rest =>
      if op.text == "→" || op.text == "->" then
        set rest
        let right ← parseFormulaTokens
        pure (.imp left right)
      else pure left
  | [] => pure left
end

/-- Parse a formula and reject trailing tokens. -/
def parseFormula (source : String) : Except ParseError Formula := do
  let tokens ← lex source
  let (formula, remaining) ← (parseFormulaTokens).run (withEndOfInput source tokens)
  if consumedInput remaining then pure formula
  else .error ⟨"Unexpected trailing input", remaining.head!.position⟩

private partial def parseProofTokens : Parser Proof := do
  let name ← takeName
  match name with
  | "hyp" => do
      takeToken "("
      let formula ← parseFormulaTokens
      takeToken ")"
      pure (.hypothesis formula)
  | "intro" => do
      let assumption ← parseFormulaTokens
      takeToken "="
      takeToken ">"
      let body ← parseProofTokens
      pure (.impIntro assumption body)
  | "apply" | "pair" => do
      takeToken "("
      let left ← parseProofTokens
      takeToken ","
      let right ← parseProofTokens
      takeToken ")"
      if name == "apply" then pure (.impElim left right) else pure (.andIntro left right)
  | "left" | "right" => do
      takeToken "("
      let proof ← parseProofTokens
      takeToken ")"
      if name == "left" then pure (.andLeft proof) else pure (.andRight proof)
  | "inl" | "inr" => do
      takeToken "["
      let other ← parseFormulaTokens
      takeToken "]"
      takeToken "("
      let proof ← parseProofTokens
      takeToken ")"
      if name == "inl" then pure (.orLeft other proof) else pure (.orRight other proof)
  | "absurd" => do
      takeToken "["
      let target ← parseFormulaTokens
      takeToken "]"
      takeToken "("
      let proof ← parseProofTokens
      takeToken ")"
      pure (.falseElim target proof)
  | "cases" => do
      takeToken "("
      let scrutinee ← parseProofTokens
      takeToken ";"
      let leftAssumption ← parseFormulaTokens
      takeToken "="; takeToken ">"
      let leftCase ← parseProofTokens
      takeToken ";"
      let rightAssumption ← parseFormulaTokens
      takeToken "="; takeToken ">"
      let rightCase ← parseProofTokens
      takeToken ")"
      pure (.orElim scrutinee leftAssumption leftCase rightAssumption rightCase)
  | _ => fail s!"Unknown proof form '{name}'"

/-- Parse a proof term and reject trailing tokens. -/
def parseProof (source : String) : Except ParseError Proof := do
  let tokens ← lex source
  let (proof, remaining) ← (parseProofTokens).run (withEndOfInput source tokens)
  if consumedInput remaining then pure proof
  else .error ⟨"Unexpected trailing input", remaining.head!.position⟩

end MiniLean
