/-!
# MiniLean.Checker

An executable type checker for MiniLean proof terms. `inferDetailed` reports
why a proof term is malformed; the `infer` and `check` wrappers retain the
small `Option` and `Bool` interface used by existing clients.
-/

import MiniLean.Core

namespace MiniLean

/-- A precise reason why a proof term failed to type check. -/
inductive CheckError where
  | missingAssumption (formula : Formula)
  | expectedImplication (actual : Formula)
  | argumentMismatch (expected actual : Formula)
  | expectedConjunction (actual : Formula)
  | expectedDisjunction (actual : Formula)
  | caseAssumptionMismatch (side : String) (expected actual : Formula)
  | caseResultMismatch (leftResult rightResult : Formula)
  | expectedFalse (actual : Formula)
  | goalMismatch (expected actual : Formula)
  deriving Repr, DecidableEq

/-- Check whether a formula appears in the context. -/
def Context.contains (ctx : Context) (p : Formula) : Bool :=
  ctx.any fun assumption => decide (assumption = p)

/-- Infer a proof term's conclusion, reporting the rule that failed. -/
def inferDetailed (ctx : Context) : Proof → Except CheckError Formula
  | .hypothesis p =>
      if ctx.contains p then .ok p else .error (.missingAssumption p)
  | .impIntro assumption body => do
      let conclusion ← inferDetailed (ctx.extend assumption) body
      pure (.imp assumption conclusion)
  | .impElim function argument => do
      let functionType ← inferDetailed ctx function
      let argumentType ← inferDetailed ctx argument
      match functionType with
      | .imp input output =>
          if input == argumentType then .ok output
          else .error (.argumentMismatch input argumentType)
      | _ => .error (.expectedImplication functionType)
  | .andIntro left right => do
      let leftType ← inferDetailed ctx left
      let rightType ← inferDetailed ctx right
      pure (.and leftType rightType)
  | .andLeft pair => do
      match ← inferDetailed ctx pair with
      | .and left _ => pure left
      | actual => .error (.expectedConjunction actual)
  | .andRight pair => do
      match ← inferDetailed ctx pair with
      | .and _ right => pure right
      | actual => .error (.expectedConjunction actual)
  | .orLeft other proof => do
      let left ← inferDetailed ctx proof
      pure (.or left other)
  | .orRight other proof => do
      let right ← inferDetailed ctx proof
      pure (.or other right)
  | .orElim disjunction leftAssumption leftCase rightAssumption rightCase => do
      let disjunctionType ← inferDetailed ctx disjunction
      match disjunctionType with
      | .or left right => do
          if left != leftAssumption then
            throw (.caseAssumptionMismatch "left" left leftAssumption)
          if right != rightAssumption then
            throw (.caseAssumptionMismatch "right" right rightAssumption)
          let leftResult ← inferDetailed (ctx.extend leftAssumption) leftCase
          let rightResult ← inferDetailed (ctx.extend rightAssumption) rightCase
          if leftResult == rightResult then .ok leftResult
          else .error (.caseResultMismatch leftResult rightResult)
      | actual => .error (.expectedDisjunction actual)
  | .falseElim target proof => do
      match ← inferDetailed ctx proof with
      | .falsum => pure target
      | actual => .error (.expectedFalse actual)

/-- Check a proof against a goal while preserving detailed failure information. -/
def checkDetailed (goal : Formula) (proof : Proof) : Except CheckError Unit := do
  let actual ← inferDetailed [] proof
  if actual == goal then .ok () else .error (.goalMismatch goal actual)

/-- Infer a proof term's conclusion, rejecting malformed terms with `none`. -/
def infer (ctx : Context) (proof : Proof) : Option Formula :=
  (inferDetailed ctx proof).toOption

/-- Accept a proof only when its inferred conclusion matches the requested goal. -/
def check (goal : Formula) (proof : Proof) : Bool :=
  match checkDetailed goal proof with
  | .ok _ => true
  | .error _ => false

end MiniLean
