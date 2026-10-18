import Signatures.Runtime.Caliper.FoldNames
import Signatures.Runtime.Caliper.ExpressionBounds

/-! All accepted original expressions have derived register/descriptor bounds.
Only primitive implementations and executed final conversions supply name bounds;
composition, branching and fold metadata are accounted by the compiler proof. -/

namespace Signatures.Runtime.CaliperBackend.SourceExpression

open Caliper BoundedSource

variable {w : Nat} {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
    {P : Primitives base Op} {hw : 16 < 2 ^ w}

theorem Variable.names {Γ : List (Ty Atom)} {a : Ty Atom} {v : Var Γ a}
    {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    (access : Variable v input output) (hw : 16 < 2 ^ w) (slots : Nat) :
    NamesAccounted (access.compile (cost := .unit) (by decide) hw).program.code slots := by
  induction access with
  | here head tail fits => exact Implementation.first_names head tail hw fits slots
  | there head rest fits ih => exact (Implementation.second_names head _ hw fits slots).seq ih

/-- A uniform dense name limit for the supplied leaves. It does not assert any
bound on a finished expression's generated code. -/
def Compilation.PrimitiveNames (slots : Nat) {Γ : List (Ty Atom)} {a : Ty Atom}
    {expression : Expr Op Γ a} {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)} :
    Compilation P .unit hw expression input output → Prop
  | .var _ | .unit _ | .bool _ _ | .nat _ _ _ _ _ | .nil _ _ _ _ _ => True
  | .pair first second _ _ _ => first.PrimitiveNames slots ∧ second.PrimitiveNames slots
  | .fst _ _ _ code | .snd _ _ _ code => code.PrimitiveNames slots
  | .cons _ _ _ _ head tail _ _ => head.PrimitiveNames slots ∧ tail.PrimitiveNames slots
  | .branch test yes no _ _ => test.PrimitiveNames slots ∧ yes.PrimitiveNames slots ∧ no.PrimitiveNames slots
  | .letE _ _ _ binding code => binding.PrimitiveNames slots ∧ code.PrimitiveNames slots
  | .op _ implementation code => code.PrimitiveNames slots ∧ NamesBound implementation.program.code slots
  | .fold _ _ _ _ _ _ _ values initial body => values.PrimitiveNames slots ∧ initial.PrimitiveNames slots ∧ body.PrimitiveNames slots
  | .foldStages _ _ _ _ _ _ _ _ values initial bodies stops =>
      values.PrimitiveNames slots ∧ initial.PrimitiveNames slots ∧
        (∀ i, (bodies i).PrimitiveNames slots) ∧ (∀ i, NamesBound (stops i).program.code slots)
  | .view code _ _ | .listWiden _ _ _ _ _ _ code => code.PrimitiveNames slots

theorem Compilation.names {Γ : List (Ty Atom)} {a : Ty Atom}
    {expression : Expr Op Γ a} {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    (certificate : Compilation P .unit hw expression input output) (slots : Nat) (bounds : certificate.PrimitiveNames slots)
    (implementation : Implementation .unit input output (expression.denote P))
    (compiled : certificate.compile (by decide) = some implementation) :
    NamesAccounted implementation.program.code slots := by
  induction certificate with
  | var access =>
    cases Option.some.inj compiled
    exact access.names hw slots
  | unit input =>
    cases Option.some.inj compiled
    exact DataImplementation.unit_names input hw slots
  | bool input value =>
    cases Option.some.inj compiled
    exact DataImplementation.boolean_names input value hw slots
  | nat input value bound fits valid =>
    cases Option.some.inj compiled
    exact Natural.constant_names input bound value hw fits valid slots
  | pair first second duplicateFits middleFits outputFits ih₁ ih₂ =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨left, gotLeft, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨right, gotRight, compiled⟩ := compiled
    exact Implementation.checkedPair_names left right hw duplicateFits middleFits outputFits
      (ih₁ bounds.1 left gotLeft) (ih₂ bounds.2 right gotRight) implementation compiled
  | fst left right fits code ih =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨pair, gotPair, compiled⟩ := compiled
    cases Option.some.inj compiled
    exact (ih bounds pair gotPair).seq (Implementation.first_names left right hw fits slots)
  | snd left right fits code ih =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨pair, gotPair, compiled⟩ := compiled
    cases Option.some.inj compiled
    exact (ih bounds pair gotPair).seq (Implementation.second_names left right hw fits slots)
  | nil input entry capacity countFits storageFits =>
    cases Option.some.inj compiled
    exact ListData.empty_names input entry capacity hw countFits storageFits slots
  | cons entry capacity countFits storageFits headCode tailCode duplicateFits middleFits ih₁ ih₂ =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨head, gotHead, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨tail, gotTail, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨frame, gotFrame, compiled⟩ := compiled
    cases Option.some.inj compiled
    exact (Implementation.checkedPair_names head tail hw duplicateFits middleFits _
      (ih₁ bounds.1 head gotHead) (ih₂ bounds.2 tail gotTail) frame gotFrame).seq
      (ListData.cons_names entry capacity hw countFits storageFits slots)
  | branch test left right duplicateFits tagFits ihTest ihLeft ihRight =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨condition, gotCondition, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨yes, gotYes, compiled⟩ := compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨no, gotNo, compiled⟩ := compiled
    exact Implementation.checkedBranch_names (hw := hw) condition yes no duplicateFits tagFits
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
    exact (Implementation.checkedPair_names value (Implementation.identity _ (width_pos hw)) hw
      duplicateFits frameFits frameFits (ihBinding bounds.1 value gotValue)
      (skip_names slots) frame gotFrame).seq (ihCode bounds.2 body gotBody)
  | op instr primitive code ih =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨argument, gotArgument, compiled⟩ := compiled
    cases Option.some.inj compiled
    exact (ih bounds.1 argument gotArgument).seq bounds.2.accounted
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
      have accumulatorBound := Implementation.checkedPair_names initial (Implementation.identity input (width_pos hw)) hw _ _ _
        (ihInitial bounds.2.1 initial gotInitial) (skip_names slots) accumulator gotAccumulator
      have frameBound := Implementation.checkedPair_names values accumulator hw _ _ _
        (ihValues bounds.1 values gotValues) accumulatorBound frame gotFrame
      exact frameBound.seq (FoldImplementation.compile_names entry state input argFits body hw nameFits capacity countFits frameFits
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
    have accumulatorBound := Implementation.checkedPair_names initial (Implementation.identity input (width_pos hw)) hw _ _ _
      (ihInitial bounds.2.1 initial gotInitial) (skip_names slots) accumulator gotAccumulator
    have frameBound := Implementation.checkedPair_names values accumulator hw _ _ _
      (ihValues bounds.1 values gotValues) accumulatorBound frame gotFrame
    have foldBound := StagedFold.compile_names entry output input hw _ capacity states countFits argFits frameFits
      (fun i => (bodyCode i).compile (by decide)) stops slots
      (fun i body got => ihBody i (bounds.2.2.1 i) body got)
      (fun i => (bounds.2.2.2 i).accounted) fold gotFold
    exact frameBound.seq foldBound
  | view code preserves sameBytes ih =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨body, gotBody, compiled⟩ := compiled
    cases Option.some.inj compiled
    exact (ih bounds body gotBody).seq (skip_names slots)
  | listWiden entry source target increasing countFits storageFits code ih =>
    dsimp only [Compilation.compile] at compiled
    erw [Option.bind_eq_some_iff] at compiled
    obtain ⟨body, gotBody, compiled⟩ := compiled
    cases Option.some.inj compiled
    exact (ih bounds body gotBody).seq (ListData.widen_names entry source target increasing hw countFits storageFits slots)

end Signatures.Runtime.CaliperBackend.SourceExpression
