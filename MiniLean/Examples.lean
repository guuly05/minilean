/-!
# MiniLean.Examples

Some proof terms built from MiniLean's primitive rules.
-/

import MiniLean.Checker

namespace MiniLean.Examples

open MiniLean

def p : Formula := .atom 0
def q : Formula := .atom 1
def r : Formula := .atom 2

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

/-- Introduce the left side of a disjunction, then eliminate it by cases. -/
def orIdentity : Proof :=
  .impIntro p <| .orElim (.orLeft q (.hypothesis p)) p (.hypothesis p) q (.hypothesis q)

/-- Falsehood can be eliminated to any target formula. -/
def explosion : Proof :=
  .impIntro .falsum <| .falseElim r (.hypothesis .falsum)

#eval check (.imp p p) identity
#eval check (.imp (.imp p q) (.imp p q)) modusPonens
#eval check (.imp (.and p q) (.and q p)) swapConjunction
#eval check (.imp .falsum (.neg p)) falseImpliesNot
#eval check (.imp p (.iff p p)) iffReflexive
#eval check (.imp p (.or p q)) orIdentity
#eval check (.imp .falsum r) explosion

/-- Context lookup works for any member, not only the first assumption. -/
#eval inferDetailed [p, q] (.hypothesis q)

/-- Extending with an existing assumption is permitted and preserves lookup. -/
#eval inferDetailed ([p] : Context).extend p (.hypothesis p)

/-- A rejected term reports its missing local assumption. -/
def missingHypothesis : Proof := .hypothesis q

/-- Applying a function to a proof of the wrong premise is rejected. -/
def wrongImplicationArgument : Proof :=
  .impElim (.hypothesis (.imp p q)) (.hypothesis r)

/-- Implication elimination also rejects a function that is not an implication. -/
def applyNonImplication : Proof := .impElim (.hypothesis p) (.hypothesis p)

/-- Both branches of disjunction elimination must prove the same result. -/
def mismatchedCases : Proof :=
  .orElim (.hypothesis (.or p q)) p (.hypothesis p) q (.hypothesis q)

/-- A case assumption must match the corresponding disjunct. -/
def wrongCaseAssumption : Proof :=
  .orElim (.hypothesis (.or p q)) q (.hypothesis q) q (.hypothesis q)

/-- Projection requires a conjunction. -/
def projectNonConjunction : Proof := .andLeft (.hypothesis p)

/-- Falsehood elimination requires a proof of falsehood. -/
def eliminateNonFalse : Proof := .falseElim q (.hypothesis p)

/-- Case analysis requires a proof of a disjunction. -/
def eliminateNonDisjunction : Proof :=
  .orElim (.hypothesis p) p (.hypothesis p) q (.hypothesis q)

#eval inferDetailed [] missingHypothesis
#eval checkDetailed (.imp q q) identity
#eval inferDetailed [.imp p q, r] wrongImplicationArgument
#eval inferDetailed [p] applyNonImplication
#eval inferDetailed [.or p q] mismatchedCases
#eval inferDetailed [.or p q] wrongCaseAssumption
#eval inferDetailed [p] projectNonConjunction
#eval inferDetailed [p] eliminateNonFalse
#eval inferDetailed [p, q] eliminateNonDisjunction

end MiniLean.Examples
