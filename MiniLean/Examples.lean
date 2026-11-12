/-!
# MiniLean.Examples

Some proof terms built from MiniLean's primitive rules.
-/

import MiniLean.Checker

namespace MiniLean.Examples

open MiniLean

def p : Formula := .atom 0
def q : Formula := .atom 1

/-- The identity theorem: `P → P`. -/
def identity : Proof := .impIntro p (.hypothesis p)

/-- Given `P → Q` and `P`, derive `Q`. -/
def modusPonens : Proof :=
  .impIntro (.imp p q) <| .impIntro p <| .impElim (.hypothesis (.imp p q)) (.hypothesis p)

/-- From `P ∧ Q`, derive `Q ∧ P`. -/
def swapConjunction : Proof :=
  .impIntro (.and p q) <| .andIntro (.andRight (.hypothesis (.and p q))) (.andLeft (.hypothesis (.and p q)))

/-- Negation is implication to falsehood, so the existing implication rule
proves `P → ¬P` whenever `P` itself is falsehood. -/
def falseImpliesNot : Proof :=
  .impIntro .falsum <| .impIntro p <| .falseElim .falsum (.hypothesis .falsum)

/-- The biconditional abbreviation exposes both directions as a conjunction. -/
def iffReflexive : Proof :=
  .impIntro p <| .andIntro (.impIntro p (.hypothesis p)) (.impIntro p (.hypothesis p))

#eval check (.imp p p) identity
#eval check (.imp (.imp p q) (.imp p q)) modusPonens
#eval check (.imp (.and p q) (.and q p)) swapConjunction
#eval check (.imp .falsum (.neg p)) falseImpliesNot
#eval check (.imp p (.iff p p)) iffReflexive

/-- A rejected term reports its missing local assumption. -/
def missingHypothesis : Proof := .hypothesis q

#eval inferDetailed [] missingHypothesis
#eval checkDetailed (.imp q q) identity

end MiniLean.Examples
