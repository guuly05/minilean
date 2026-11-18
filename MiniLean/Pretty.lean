import MiniLean.Checker

/-!
# MiniLean.Pretty

Readable, deterministic rendering for MiniLean formulas and proof terms.
-/

namespace MiniLean

private def Formula.renderPrec : Formula → Nat → String
  | .atom id, _ => s!"P{id}"
  | .falsum, _ => "⊥"
  | .imp left right, prec =>
      let rendered := s!"{Formula.renderPrec left 2} → {Formula.renderPrec right 1}"
      if prec > 1 then s!"({rendered})" else rendered
  | .and left right, prec =>
      let rendered := s!"{Formula.renderPrec left 3} ∧ {Formula.renderPrec right 3}"
      if prec > 2 then s!"({rendered})" else rendered
  | .or left right, prec =>
      let rendered := s!"{Formula.renderPrec left 4} ∨ {Formula.renderPrec right 4}"
      if prec > 3 then s!"({rendered})" else rendered

/-- Render a formula using `P<n>` atom names and precedence-aware Unicode operators.
Implication is right associative; conjunction binds more tightly than disjunction.
-/
def Formula.pretty (formula : Formula) : String := Formula.renderPrec formula 0

/-- Render proof constructors compactly, with child terms nested in parentheses. -/
def Proof.pretty : Proof → String
  | .hypothesis formula => s!"hyp({formula.pretty})"
  | .impIntro assumption body => s!"intro {assumption.pretty} => {body.pretty}"
  | .impElim function argument => s!"apply({function.pretty}, {argument.pretty})"
  | .andIntro left right => s!"pair({left.pretty}, {right.pretty})"
  | .andLeft pair => s!"left({pair.pretty})"
  | .andRight pair => s!"right({pair.pretty})"
  | .orLeft other proof => s!"inl[{other.pretty}]({proof.pretty})"
  | .orRight other proof => s!"inr[{other.pretty}]({proof.pretty})"
  | .orElim disjunction leftAssumption leftCase rightAssumption rightCase =>
      s!"cases({disjunction.pretty}; {leftAssumption.pretty} => {leftCase.pretty}; {rightAssumption.pretty} => {rightCase.pretty})"
  | .falseElim target proof => s!"absurd[{target.pretty}]({proof.pretty})"

end MiniLean
