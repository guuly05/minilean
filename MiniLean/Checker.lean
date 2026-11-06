/-!
# MiniLean.Checker

An executable type checker for MiniLean proof terms. `infer` either returns
the formula proved by a term or rejects it with `none`.
-/

import MiniLean.Core

namespace MiniLean

/-- Check whether a formula appears in the context. -/
def Context.contains (ctx : Context) (p : Formula) : Bool :=
  ctx.any fun assumption => decide (assumption = p)

/-- Infer a proof term's conclusion, rejecting malformed applications. -/
def infer (ctx : Context) : Proof → Option Formula
  | .hypothesis p =>
      if ctx.contains p then some p else none
  | .impIntro assumption body => do
      let conclusion ← infer (assumption :: ctx) body
      pure (.imp assumption conclusion)
  | .impElim function argument => do
      let functionType ← infer ctx function
      let argumentType ← infer ctx argument
      match functionType with
      | .imp input output =>
          if input == argumentType then some output else none
      | _ => none
  | .andIntro left right => do
      let leftType ← infer ctx left
      let rightType ← infer ctx right
      pure (.and leftType rightType)
  | .andLeft pair => do
      match ← infer ctx pair with
      | .and left _ => pure left
      | _ => none
  | .andRight pair => do
      match ← infer ctx pair with
      | .and _ right => pure right
      | _ => none
  | .orLeft other proof => do
      let left ← infer ctx proof
      pure (.or left other)
  | .orRight other proof => do
      let right ← infer ctx proof
      pure (.or other right)
  | .orElim disjunction leftAssumption leftCase rightAssumption rightCase => do
      let disjunctionType ← infer ctx disjunction
      match disjunctionType with
      | .or left right => do
          let leftResult ← infer (leftAssumption :: ctx) leftCase
          let rightResult ← infer (rightAssumption :: ctx) rightCase
          if left == leftAssumption && right == rightAssumption && leftResult == rightResult then
            some leftResult
          else
            none
      | _ => none
  | .falseElim target proof => do
      match ← infer ctx proof with
      | .falsum => pure target
      | _ => none

/-- Accept a proof only when its inferred conclusion matches the requested goal. -/
def check (goal : Formula) (proof : Proof) : Bool :=
  (infer [] proof).map (· == goal) |>.getD false

end MiniLean
