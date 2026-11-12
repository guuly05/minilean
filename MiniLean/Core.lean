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

/-- Negation is represented by implication to falsehood. -/
def Formula.neg (p : Formula) : Formula := .imp p .falsum

/-- A biconditional is represented by implications in both directions. -/
def Formula.iff (p q : Formula) : Formula :=
  .and (.imp p q) (.imp q p)

instance : Inhabited Formula := ⟨Formula.falsum⟩

/-- A local context is a list of assumptions. -/
abbrev Context := List Formula

/-- Add an assumption at the front of a context. Duplicate assumptions are
permitted; lookup is membership-based, so duplicates do not change which
hypotheses can be used. -/
def Context.extend (ctx : Context) (assumption : Formula) : Context :=
  assumption :: ctx

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
