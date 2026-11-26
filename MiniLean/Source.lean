import MiniLean.Parser
import MiniLean.Checker

/-!
# MiniLean.Source

The line-oriented source file format and declaration checker.
-/

namespace MiniLean

structure SourceResult where
  name : String
  accepted : Bool
  deriving Repr, DecidableEq

private def sourceError (line column : Nat) (message : String) : ParseError :=
  ⟨message, ⟨line, column⟩⟩

private def trim (value : String) : String :=
  let chars := value.toList.dropWhile Char.isWhitespace
  String.intercalate "" ((chars.reverse.dropWhile Char.isWhitespace).reverse.map String.singleton)

private def adjustError (line column : Nat) (err : ParseError) : ParseError :=
  ⟨err.message, ⟨line + err.position.line - 1,
    if err.position.line == 1 then column + err.position.column - 1 else err.position.column⟩⟩

private def parseDeclaration (lineNo : Nat) (line : String) : Except ParseError (String × Formula × Proof) := do
  let trimmed := trim line
  if !trimmed.startsWith "theorem " then
    throw <| sourceError lineNo 1 "Expected a theorem declaration"
  let rest := trimmed.drop 8
  let nameParts := rest.splitOn " : "
  if nameParts.length < 2 then
    throw <| sourceError lineNo 9 "Expected ':' after theorem name"
  let name := nameParts[0]!
  if name.isEmpty || !(name.toList.head!.isAlpha || name.toList.head! == '_') ||
      name.toList.any (fun c => !(c.isAlphanum || c == '_')) then
    throw <| sourceError lineNo 9 "Invalid theorem name"
  let afterName := nameParts[1]!
  let pieces := afterName.splitOn " := "
  if pieces.length != 2 then
    throw <| sourceError lineNo (10 + name.length) "Expected ':=' before the proof term"
  let formulaText := pieces[0]!
  let proofText := pieces[1]!
  let formulaColumn := 10 + name.length
  let proofColumn := formulaColumn + formulaText.length + 4
  let formula ← (parseFormula formulaText).mapError (adjustError lineNo formulaColumn)
  let proof ← (parseProof proofText).mapError (adjustError lineNo proofColumn)
  pure (name, formula, proof)

/-- Parse and check one theorem declaration per nonblank, noncomment line.
Lines beginning with `--` are ignored. -/
def checkSource (source : String) : Except ParseError (List SourceResult) := do
  let mut results := []
  let mut seen : List String := []
  for (line, index) in source.splitOn "\n" |>.zipIdx do
    let lineNo := index + 1
    let trimmed := trim line
    if trimmed.isEmpty || trimmed.startsWith "--" then continue
    let (name, formula, proof) ← parseDeclaration lineNo line
    if seen.contains name then
      throw <| sourceError lineNo 9 s!"Duplicate theorem '{name}'"
    seen := name :: seen
    results := results ++ [⟨name, check formula proof⟩]
  pure results

end MiniLean
