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

#eval check (.imp p p) identity
#eval check (.imp (.imp p q) (.imp p q)) modusPonens
#eval check (.imp (.and p q) (.and q p)) swapConjunction

end MiniLean.Examples
