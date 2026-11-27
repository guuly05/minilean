import MiniLean.Checker
import MiniLean.Pretty

/-!
# MiniLean.Tactic

A small structured tactic language. Branching tactics contain child scripts,
so each subgoal is solved explicitly and deterministically.
-/

namespace MiniLean

/-- Tactic scripts represented as a tree, with one child script per subgoal. -/
inductive Tactic where
  | assumption
  | exact (proof : Proof)
  | intro (body : Tactic)
  | apply (function : Proof) (argument : Tactic)
  | andIntro (left right : Tactic)
  | andLeft (pair : Proof)
  | andRight (pair : Proof)
  deriving Repr

/-- A tactic failure with the goal or rule that could not be handled. -/
inductive TacticError where
  | assumptionNotFound (goal : Formula)
  | exactRejected (error : CheckError)
  | introExpectedImplication (goal : Formula)
  | applyExpectedImplication (actual : Formula)
  | applyResultMismatch (goal actual : Formula)
  | andIntroExpectedConjunction (goal : Formula)
  | projectionExpectedConjunction (actual : Formula)
  | projectionGoalMismatch (goal actual : Formula)
  deriving Repr, DecidableEq

/-- Current goal display, including the local assumptions available to tactics. -/
def Tactic.goalPretty (ctx : Context) (goal : Formula) : String :=
  let assumptions := ctx.map Formula.pretty
  let contextText := if assumptions.isEmpty then "(no assumptions)"
    else String.intercalate ", " assumptions
  s!"{contextText}\n⊢ {Formula.pretty goal}"

private def checkInContext (ctx : Context) (goal : Formula) (proof : Proof) :
    Except TacticError Proof := do
  let actual ← (inferDetailed ctx proof).mapError TacticError.exactRejected
  if actual == goal then pure proof
  else throw (.exactRejected (.goalMismatch goal actual))

/-- Run a tactic tree and return a proof term accepted by the core checker. -/
def runTactic (ctx : Context) (goal : Formula) : Tactic → Except TacticError Proof
  | .assumption =>
      if ctx.contains goal then pure (.hypothesis goal)
      else .error (.assumptionNotFound goal)
  | .exact proof => checkInContext ctx goal proof
  | .intro body =>
      match goal with
      | .imp premise conclusion => do
          let proof ← runTactic (Context.extend ctx premise) conclusion body
          pure (.impIntro premise proof)
      | _ => .error (.introExpectedImplication goal)
  | .apply function argument => do
      let functionType ← (inferDetailed ctx function).mapError TacticError.exactRejected
      match functionType with
      | .imp premise result =>
          if result != goal then throw (.applyResultMismatch goal result)
          let argumentProof ← runTactic ctx premise argument
          pure (.impElim function argumentProof)
      | actual => .error (.applyExpectedImplication actual)
  | .andIntro left right =>
      match goal with
      | .and leftGoal rightGoal => do
          let leftProof ← runTactic ctx leftGoal left
          let rightProof ← runTactic ctx rightGoal right
          pure (.andIntro leftProof rightProof)
      | _ => .error (.andIntroExpectedConjunction goal)
  | .andLeft pair => do
      let pairType ← (inferDetailed ctx pair).mapError TacticError.exactRejected
      match pairType with
      | .and left _ =>
          if left == goal then pure (.andLeft pair)
          else .error (.projectionGoalMismatch goal left)
      | actual => .error (.projectionExpectedConjunction actual)
  | .andRight pair => do
      let pairType ← (inferDetailed ctx pair).mapError TacticError.exactRejected
      match pairType with
      | .and _ right =>
          if right == goal then pure (.andRight pair)
          else .error (.projectionGoalMismatch goal right)
      | actual => .error (.projectionExpectedConjunction actual)

/-- Run a closed tactic script and confirm its result against the goal. -/
def solve (goal : Formula) (script : Tactic) : Except TacticError Proof := do
  let proof ← runTactic [] goal script
  match checkDetailed goal proof with
  | .ok _ => pure proof
  | .error err => throw (.exactRejected err)

end MiniLean
