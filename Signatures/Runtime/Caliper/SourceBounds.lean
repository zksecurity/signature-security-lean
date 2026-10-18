import Signatures.Runtime.Caliper.SourceErasure
import Signatures.Runtime.Caliper.InteractiveControlBounds
import Signatures.Runtime.Caliper.CountedBounds

/-! Uniform runtime of the compiled source language, derived structurally from
actual Caliper primitive bounds. This does not import the old abstract cost table
or assume that a completed reduction is efficient. Program families still need
polynomial bounds on these primitive budgets, widths and loop limits.
-/

namespace Signatures.Runtime.CaliperBackend.SourceCompilation

open Caliper OracleComp OracleSpec PFunctor BoundedSource

universe v u

variable {w : Nat} {I : Type} {spec : OracleSpec I}
    {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
    {Q : QuantitativeStepClass.{0, v, u} C} {sourceIface : BackendProgram.Interface (C := C) spec}
    {targetIface : Interface w spec} {cost : WordIO.Costs} {hw : 16 < 2 ^ w}

/-- Only primitive leaves need supplied bounds. Every control budget is computed
from the generated code, including the oracle adapter and saved-state copying. -/
def Compilation.LocalBounds {A B : Type} {a : C.Str A} {b : C.Str B}
    {source : BackendProgram.Code Q spec sourceIface a b} {input : Layout w A} {output : Layout w B} :
    Compilation targetIface cost hw source input output → Type
  | .atomic _ implementation => {budget : Nat // ∀ value, implementation.program.time value ≤ budget}
  | .query => Unit
  | .seq initial following => initial.LocalBounds × following.LocalBounds
  | .branch initial following _ => initial.LocalBounds × following.LocalBounds
  | .first _ _ body _ _ => body.LocalBounds
  | .loop _ body stop _ => body.LocalBounds × stop.LocalBounds
  | .iterate _ body _ _ _ => body.LocalBounds

def Compilation.timeBudget {A B : Type} {a : C.Str A} {b : C.Str B}
    {source : BackendProgram.Code Q spec sourceIface a b} {input : Layout w A} {output : Layout w B}
    (code : Compilation targetIface cost hw source input output) : code.LocalBounds → Nat :=
  match code with
  | .atomic _ _ => fun bound => bound.val
  | .query => fun _ => WordIO.exchangeTime cost targetIface.request.representation.encoding.words targetIface.reply.encoding.words
  | .seq initial following => fun bounds => initial.timeBudget bounds.1 + following.timeBudget bounds.2
  | .branch (leftInput := left) (rightInput := right) initial following _ => fun bounds =>
      Interactive.dispatchTime (w := w) cost left.representation.encoding.words right.representation.encoding.words
        (initial.timeBudget bounds.1) (following.timeBudget bounds.2)
  | .first (input := input) (output := output) _ saved body _ _ => fun bounds =>
      (Retain.prepare (w := w) (Interactive.savedBuffer targetIface.port body.compile)
        input.representation.encoding.words saved.representation.encoding.words).staticTime cost.machine +
      (body.timeBudget bounds + (Retain.finish (w := w) (Interactive.savedBuffer targetIface.port body.compile)
        output.representation.encoding.words saved.representation.encoding.words).staticTime cost.machine)
  | .loop (state := state) (result := result) _ body stop fuel => fun bounds =>
      stop.timeBudget bounds.2 + fuel * (body.timeBudget bounds.1 +
        Interactive.loopOverhead (w := w) cost result.representation.encoding.words state.representation.encoding.words)
  | .iterate (state := state) _ body fuel _ _ => fun bounds =>
      Interactive.Counted.budget (w := w) cost (Interactive.savedBuffer targetIface.port body.compile)
        state.representation.encoding.words (body.timeBudget bounds) fuel

theorem Compilation.timeBound {A B : Type} {a : C.Str A} {b : C.Str B}
    {source : BackendProgram.Code Q spec sourceIface a b} {input : Layout w A} {output : Layout w B}
    (code : Compilation targetIface cost hw source input output) (bounds : code.LocalBounds)
    (allocation : 1 ≤ cost.machine.allocPerWord) :
    Interactive.TimeBound targetIface.port cost input.representation code.compile (code.timeBudget bounds) := by
  induction code with
  | atomic source implementation => exact Interactive.TimeBound.compute implementation.program bounds.val bounds.property
  | query => exact Interactive.TimeBound.query
  | seq first second ih₁ ih₂ => exact (ih₁ bounds.1).seq (first.correct allocation) (ih₂ bounds.2)
  | @branch A B D a b d left right leftInput rightInput output first second fits ih₁ ih₂ =>
    exact ((ih₁ bounds.1).dispatch leftInput.representation rightInput.representation (ih₂ bounds.2) (width_pos hw) fits).viewInput
      (leftInput.sum rightInput (width_pos hw) fits).representation (sumView leftInput rightInput) (fun _ => rfl)
  | @first A B S a b s body input output saved code inputFits outputFits ih =>
    exact ((ih bounds).retain (code.correct allocation) allocation saved.representation hw inputFits).viewInput
      (input.prod saved inputFits).representation (productView input saved) (fun _ => rfl)
  | @loop S B s b body stop state result fits step finish fuel ihBody ihStop =>
    have viewed := (step.correct allocation).viewOutput (result.representation.sum state.representation (width_pos hw) fits)
      (sumView result state) (fun _ => rfl)
    exact Interactive.TimeBound.loop state.representation result.representation (width_pos hw) fits viewed
      (ihBody bounds.1) (ihStop bounds.2) fuel
  | @iterate S s counter body state code fuel counterFits storageFits ih =>
    exact (Interactive.Counted.timeBound state.representation (code.correct allocation) (ih bounds) allocation hw
      storageFits fuel counterFits).viewInput
        (iterationInput state fuel hw counterFits storageFits).representation (iterationView state fuel) (fun _ => rfl)

/-- Every reachable compiled result has uniformly bounded actual running time
and additional buffer capacity. Source refinement separately rules out failures.
This deliberately does not call the time budget a total-memory bound. -/
theorem Compilation.resources {A B : Type} {a : C.Str A} {b : C.Str B}
    {source : BackendProgram.Code Q spec sourceIface a b} {input : Layout w A} {output : Layout w B}
    (code : Compilation targetIface cost hw source input output) (bounds : code.LocalBounds)
    (allocation : 1 ≤ cost.machine.allocPerWord)
    (tape : RandomTape w) (value : input.Value) (before : State w) (holds : input.representation.Holds value before)
    (finished : WordIO.Result w) (reached : some finished ∈ support (code.compile.execute targetIface.port cost tape before)) :
    finished.time ≤ code.timeBudget bounds ∧ finished.peak ≤ code.timeBudget bounds :=
  ⟨code.timeBound bounds allocation tape value before holds finished reached,
    (code.timeBound bounds allocation).bufferPeak (code.correct allocation) allocation tape value before holds finished reached⟩

end Signatures.Runtime.CaliperBackend.SourceCompilation
