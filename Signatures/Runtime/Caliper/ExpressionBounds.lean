import Signatures.Runtime.Caliper.ExpressionBudget

/-! Every accepted original-expression compilation satisfies the budget derived
from its syntax, layouts and primitive budgets. No whole-expression time or
stored-code premise is supplied. -/

namespace Signatures.Runtime.CaliperBackend.SourceExpression

open Caliper BoundedSource

variable {w : Nat} {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
    {P : Primitives base Op} {hw : 16 < 2 ^ w}

theorem Compilation.bounded {Γ : List (Ty Atom)} {a : Ty Atom}
    {expression : Expr Op Γ a} {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    (certificate : Compilation P .unit hw expression input output) (bounds : certificate.LocalBounds)
    (implementation : Implementation .unit input output (expression.denote P))
    (compiled : certificate.compile (by decide) = some implementation) :
    implementation.BoundedBy (certificate.budget bounds).time (certificate.budget bounds).words := by
  induction certificate with
  | var access =>
    cases Option.some.inj compiled
    exact access.bounded hw
  | unit input =>
    cases Option.some.inj compiled
    exact DataImplementation.unit_boundedBy input hw
  | bool input value =>
    cases Option.some.inj compiled
    exact DataImplementation.boolean_boundedBy input value hw
  | nat input value bound fits valid =>
    cases Option.some.inj compiled
    exact Natural.constant_boundedBy input bound value hw fits valid
  | pair first second duplicateFits middleFits outputFits ih₁ ih₂ =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨left, gotLeft, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨right, gotRight, compiled⟩ := compiled
    exact Implementation.checkedPair_boundedBy left right hw duplicateFits middleFits outputFits _ _ _ _
      (ih₁ bounds.1 left gotLeft) (ih₂ bounds.2 right gotRight) implementation compiled
  | fst left right fits code ih =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨pair, gotPair, compiled⟩ := compiled
    cases Option.some.inj compiled
    exact (ih bounds pair gotPair).then (Implementation.first_boundedBy left right hw fits)
  | snd left right fits code ih =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨pair, gotPair, compiled⟩ := compiled
    cases Option.some.inj compiled
    exact (ih bounds pair gotPair).then (Implementation.second_boundedBy left right hw fits)
  | nil input entry capacity countFits storageFits =>
    cases Option.some.inj compiled
    exact ListData.empty_boundedBy input entry capacity hw countFits storageFits
  | cons entry capacity countFits storageFits headCode tailCode duplicateFits middleFits ih₁ ih₂ =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨head, gotHead, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨tail, gotTail, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨frame, gotFrame, compiled⟩ := compiled
    cases Option.some.inj compiled
    exact (Implementation.checkedPair_boundedBy head tail hw duplicateFits middleFits _ _ _ _ _
      (ih₁ bounds.1 head gotHead) (ih₂ bounds.2 tail gotTail) frame gotFrame).then
      (ListData.cons_boundedBy entry capacity hw countFits storageFits)
  | branch test left right duplicateFits tagFits ihTest ihLeft ihRight =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨condition, gotCondition, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨yes, gotYes, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨no, gotNo, compiled⟩ := compiled
    exact Implementation.checkedBranch_boundedBy (hw := hw) condition yes no duplicateFits tagFits _ _ _ _ _ _
      (ihTest bounds.1 condition gotCondition) (ihLeft bounds.2.1 yes gotYes) (ihRight bounds.2.2 no gotNo)
      implementation compiled
  | letE localValue duplicateFits frameFits binding code ihBinding ihCode =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨value, gotValue, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨body, gotBody, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨frame, gotFrame, compiled⟩ := compiled
    cases Option.some.inj compiled
    exact (Implementation.checkedPair_boundedBy value (Implementation.identity _ (width_pos hw)) hw
      duplicateFits frameFits frameFits _ _ 0 1 (ihBinding bounds.1 value gotValue)
      (Implementation.identity_boundedBy _ (width_pos hw)) frame gotFrame).then (ihCode bounds.2 body gotBody)
  | op instr primitive code ih =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨argument, gotArgument, compiled⟩ := compiled
    cases Option.some.inj compiled
    exact (ih bounds.1 argument gotArgument).then bounds.2.bounded
  | fold input entry state capacity countFits argFits frameFits valuesCode initialCode bodyCode ihValues ihInitial ihBody =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨values, gotValues, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨initial, gotInitial, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨body, gotBody, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨accumulator, gotAccumulator, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨frame, gotFrame, compiled⟩ := compiled
    split at compiled
    next nameFits =>
      cases Option.some.inj compiled
      have accumulatorBound := Implementation.checkedPair_boundedBy initial (Implementation.identity input (width_pos hw)) hw _ _ _ _ _ 0 1
        (ihInitial bounds.2.1 initial gotInitial) (Implementation.identity_boundedBy input (width_pos hw)) accumulator gotAccumulator
      have frameBound := Implementation.checkedPair_boundedBy values accumulator hw _ _ _ _ _ _ _
        (ihValues bounds.1 values gotValues) accumulatorBound frame gotFrame
      exact frameBound.then (FoldImplementation.compile_boundedBy entry state input argFits body hw nameFits capacity countFits frameFits _ _
        (ihBody bounds.2.2 body gotBody))
    next rejected => contradiction
  | foldStages input entry output capacity states countFits argFits frameFits valuesCode initialCode bodyCode stops ihValues ihInitial ihBody =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨values, gotValues, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨initial, gotInitial, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨fold, gotFold, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨accumulator, gotAccumulator, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨frame, gotFrame, compiled⟩ := compiled
    cases Option.some.inj compiled
    have accumulatorBound := Implementation.checkedPair_boundedBy initial (Implementation.identity input (width_pos hw)) hw _ _ _ _ _ 0 1
      (ihInitial bounds.2.1 initial gotInitial) (Implementation.identity_boundedBy input (width_pos hw)) accumulator gotAccumulator
    have frameBound := Implementation.checkedPair_boundedBy values accumulator hw _ _ _ _ _ _ _
      (ihValues bounds.1 values gotValues) accumulatorBound frame gotFrame
    let bodyBudgets := fun i => (bodyCode i).budget (bounds.2.2.1 i)
    let stopBudgets := fun i => (bounds.2.2.2 i).estimate
    have foldBound := StagedFold.compile_boundedBy entry output input hw _ capacity states countFits argFits frameFits
      (fun i => (bodyCode i).compile (by decide)) stops
      (Budget.layoutBound entry.representation.encoding.words input.representation.encoding.words (fun i => (states i).representation.encoding.words))
      (Budget.maximum bodyBudgets).time (Budget.maximum bodyBudgets).words (Budget.maximum stopBudgets).time (Budget.maximum stopBudgets).words
      (Nat.le_max_left _ _) ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
      (fun i => (Finset.le_sup (f := fun i => (states i).representation.encoding.words) (Finset.mem_univ i)).trans
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
      (fun i body got => (ihBody i (bounds.2.2.1 i) body got).mono
        (Budget.time_le_maximum bodyBudgets i) (Budget.words_le_maximum bodyBudgets i))
      (fun i => (bounds.2.2.2 i).bounded.mono (Budget.time_le_maximum stopBudgets i) (Budget.words_le_maximum stopBudgets i)) fold gotFold
    exact frameBound.then foldBound
  | view code preserves sameBytes ih =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨body, gotBody, compiled⟩ := compiled
    cases Option.some.inj compiled
    exact (ih bounds body gotBody).then (Implementation.view_boundedBy (width_pos hw) preserves sameBytes)
  | listWiden entry source target increasing countFits storageFits code ih =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨body, gotBody, compiled⟩ := compiled
    cases Option.some.inj compiled
    exact (ih bounds body gotBody).then (ListData.widen_boundedBy entry source target increasing hw countFits storageFits)

/-- Attach the derived budget proof to the original checked compiler result. -/
def Compilation.compileBudget {Γ : List (Ty Atom)} {a : Ty Atom}
    {expression : Expr Op Γ a} {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    (certificate : Compilation P .unit hw expression input output) (bounds : certificate.LocalBounds) :
    Option {implementation : Implementation .unit input output (expression.denote P) //
      implementation.BoundedBy (certificate.budget bounds).time (certificate.budget bounds).words} :=
  match compiled : certificate.compile (by decide) with
  | none => none
  | some implementation => some ⟨implementation, certificate.bounded bounds implementation compiled⟩

theorem Compilation.compileBudget_forget {Γ : List (Ty Atom)} {a : Ty Atom}
    {expression : Expr Op Γ a} {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    (certificate : Compilation P .unit hw expression input output) (bounds : certificate.LocalBounds) :
    Subtype.val <$> certificate.compileBudget bounds = certificate.compile (by decide) := by
  unfold compileBudget
  split <;> simp_all

/-- The generated budget bounds an actual execution on every represented source
input; the result remains the original expression's denotation. -/
theorem Compilation.exec_bounded {Γ : List (Ty Atom)} {a : Ty Atom}
    {expression : Expr Op Γ a} {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    (certificate : Compilation P .unit hw expression input output) (bounds : certificate.LocalBounds)
    (implementation : Implementation .unit input output (expression.denote P))
    (compiled : certificate.compile (by decide) = some implementation)
    (tape : RandomTape w) (environment : input.Value) (before : State w)
    (represented : input.representation.Holds environment before) :
    ∃ after net peak, Caliper.Exec .unit tape implementation.program.code before after
      (implementation.program.time environment) net peak ∧
      output.representation.Holds ⟨expression.denote P environment.val, implementation.preserves environment.val environment.property⟩ after ∧
      implementation.program.time environment ≤ (certificate.budget bounds).time ∧
      net ≤ ((certificate.budget bounds).time : Int) ∧ peak ≤ (certificate.budget bounds).time :=
  (certificate.bounded bounds implementation compiled).exec (by decide) tape environment before represented

end Signatures.Runtime.CaliperBackend.SourceExpression
