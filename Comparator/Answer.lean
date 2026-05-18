import Lean

namespace Comparator

open Lean Elab Meta Term

/-- A type that captures the current setting for the `answer()` elaborator. -/
inductive AnswerSetting
  /--Default mode: `answer(sorry)` defaults to `True` when `sorry` has type `Prop`. -/
  | alwaysTrue
  /-- Default mode for `answer(foo)`: just postpones elaboration. -/
  | postpone
  /-- Elaborate `answer(foo)` by creating an auxiliary definition with value `foo`. -/
  | withAuxiliary
deriving Inhabited, ToJson, BEq

instance : ToString AnswerSetting where
  toString
    | .postpone => "postpone"
    | .withAuxiliary  => "with_auxiliary"
    | .alwaysTrue => "always_true"

instance : KVMap.Value AnswerSetting where
  toDataValue := DataValue.ofString ∘ ToString.toString
  ofDataValue?
    | .ofString "postpone" => some .postpone
    | .ofString "with_auxiliary" => some .withAuxiliary
    | .ofString "always_true" => some .alwaysTrue
    | _ => none

register_option comparator.answer : AnswerSetting := {
  defValue := .alwaysTrue
  descr := "Modifies the behaviour of the answer() elaborator."
}

def mkAnswerAnnotation (e : Expr) : Expr := mkAnnotation `answer e

def elabTermAndAnnotate (stx : TSyntax `term) (expectedType? : Option Expr)
    (postpone : Bool := false) :=
  mkAnswerAnnotation <$> do
    if postpone then
      postponeElabTerm (← `(by exact $stx)) expectedType?
    else
      elabTerm stx expectedType?

syntax "answer(" term ")" : term

/-- Indicates where the answer is in a problem statement. -/
@[term_elab «termAnswer(_)»]
def answerElab : TermElab := fun stx expectedType? => do
  match stx with
  | `(answer($a:term)) =>
    match comparator.answer.get (← getOptions) with
    | AnswerSetting.postpone => elabTermAndAnnotate a expectedType? true
    | .withAuxiliary =>
      let expr ← elabTermAndAnnotate a expectedType? >>= instantiateMVars
      let exprType ← (Meta.inferType expr) >>= instantiateMVars
      if expr.hasExprMVar || exprType.hasExprMVar then throwPostpone
      let some declName := (← read).declName?
        | throwError "Failed to find the name of the declaration"
      let answerName : Name := declName.str "_answer"
      let levelParamNames : List Name := (collectLevelParams {} exprType).params.toList
      let answerAuxiliaryDecl : DefinitionVal := {
        name := answerName
        levelParams := levelParamNames
        type := exprType
        value := expr
        hints := .abbrev
        safety := .safe
      }
      addDecl (.defnDecl answerAuxiliaryDecl) true
      return mkAnswerAnnotation (.const answerName <| levelParamNames.map Level.param)
    | .alwaysTrue =>
      -- If the answer is a `sorry` of type `Prop` then default to `True` in this setting
      if expectedType? == some (Expr.sort .zero) && a == (← `(term| sorry)) then
        return .const `True []
      else
        elabTermAndAnnotate a expectedType?
  | _ => Elab.throwUnsupportedSyntax

end Comparator
