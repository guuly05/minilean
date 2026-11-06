/-!
# MiniLean.Core

The small object language understood by MiniLean. Formulas are deliberately
syntax-only: equality on formulas is decidable, so the checker can compare
goals without relying on Lean's elaborator or simplifier.
-/

namespace MiniLean

/-- Propositions in MiniLean's starter logic. -/
inductive Formula where
  | atom : Nat → Formula
  | falsum : Formula
  | imp : Formula → Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  deriving DecidableEq, Repr

instance : Inhabited Formula := ⟨Formula.falsum⟩

/-- A local context is a list of assumptions. -/
abbrev Context := List Formula

/-- Proof terms form a small natural-deduction language. -/
inductive Proof where
  | hypothesis : Formula → Proof
  | impIntro : Formula → Proof → Proof
  | impElim : Proof → Proof → Proof
  | andIntro : Proof → Proof → Proof
  | andLeft : Proof → Proof
  | andRight : Proof → Proof
  | orLeft : Formula → Proof → Proof
  | orRight : Formula → Proof → Proof
  | orElim : Proof → Formula → Proof → Formula → Proof → Proof
  | falseElim : Formula → Proof → Proof
  deriving Repr

end MiniLean
