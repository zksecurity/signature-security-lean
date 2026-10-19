import Signatures.Runtime.Caliper.TokenEvaluationPrepareBounds

/-! One actual transcript evaluator: chronological row construction, encoded
initial accumulator, and the private-cache fold. Capacity is reserved for the
number of stored tokens, regardless of missing or surplus coefficients. -/
namespace Signatures.Runtime.CaliperBackend.TokenEvaluation
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G F : Type}
    [DecidableEq (key.Value base)] (layout : Layouts w (key.Value base) G F (val.Value base))
    (coefficientDefault : layout.rows.accumulation.coefficient.Value)
    (initial default : layout.rows.accumulation.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.rows.accumulation.combine layout.rows.accumulation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I}

def code (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (prepare layout coefficientDefault initial).program.code)
    (RowFold.code layout.rows default P comparison correct update updateBuffers reserve layout.capacity port draw)
def denote (source : OracleComp spec layout.rows.accumulation.cache.value.Value) (value : layout.input.Value) : OracleComp spec layout.rows.state.Value :=
  RowFold.denote layout.rows default P comparison correct update updateBuffers reserve source (foldValue layout coefficientDefault initial value)
omit [DecidableEq (key.Value base)] in
theorem foldValue_ready (value : layout.input.Value) (ready : layout.ready value) :
    RowFold.valid (base := base) (key := key) (val := val) layout.rows (foldValue layout coefficientDefault initial value) := by
  unfold RowFold.valid RowEvaluation.room
  rw [foldValue_length]
  exact ready

def preparedProgram : Realizer .unit layout.input.representation
    (RowFold.input layout.rows layout.capacity layout.countFits layout.foldFits) (foldValue layout coefficientDefault initial) :=
  (prepare layout coefficientDefault initial).program.viewOutput _ (foldValue layout coefficientDefault initial)
    (fun value => foldView_bytes layout (preparedValue layout coefficientDefault initial value))

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.rows.accumulation.cache.value.Value}
    {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) draw)
include drawCorrect in
theorem refines : Interactive.RefinesOn layout.ready port .unit layout.input.representation layout.rows.state.representation
    (denote layout coefficientDefault initial default P comparison correct update updateBuffers reserve source)
    (code layout coefficientDefault initial default P comparison correct update updateBuffers reserve port draw) := by
  have first := (Interactive.Refines.compute port .unit (preparedProgram layout coefficientDefault initial)).on layout.ready
  have second := RowFold.refines layout.rows default P comparison correct update updateBuffers reserve port drawCorrect
    layout.capacity layout.countFits layout.foldFits
  have composed := first.seq second (by
    intro value valid answer reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst answer
    exact foldValue_ready layout coefficientDefault initial value valid)
  convert composed using 1
  · funext value
    exact (pure_bind _ _).symm
  · rfl

def timeBudget (drawTime updateTime : Nat) : Nat :=
  prepareTime layout + RowFold.timeBudget layout.rows layout.capacity drawTime updateTime
def codeBudget (drawWords updateWords : Nat) : Nat :=
  prepareWords layout + RowFold.codeBudget layout.rows layout.capacity drawWords updateWords + 2

include drawCorrect in
theorem time_bound {drawTime updateTime updateWords : Nat}
    (drawBound : Interactive.TimeBound port .unit layout.rows.accumulation.cache.lookup.unit.representation draw drawTime)
    (updateBound : update.BoundedBy updateTime updateWords) :
    Interactive.TimeBoundOn layout.ready port .unit layout.input.representation
      (code layout coefficientDefault initial default P comparison correct update updateBuffers reserve port draw)
      (timeBudget layout drawTime updateTime) := by
  have first := (Interactive.Refines.compute port .unit (preparedProgram layout coefficientDefault initial)).on layout.ready
  have firstBound := (Interactive.TimeBound.compute (port := port) (cost := .unit)
    (preparedProgram layout coefficientDefault initial) _ (prepare_bounded layout coefficientDefault initial).time_le).on layout.ready
  exact Interactive.TimeBoundOn.seq first firstBound
    (RowFold.time_bound layout.rows default P comparison correct update updateBuffers reserve port drawCorrect
      layout.capacity layout.countFits layout.foldFits drawBound updateBound) (by
        intro value valid answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact foldValue_ready layout coefficientDefault initial value valid)

theorem code_bound (draw : Interactive.Code w) {drawWords updateTime updateWords : Nat}
    (drawBound : (draw.lower port).descriptionWords ≤ drawWords) (updateBound : update.BoundedBy updateTime updateWords) :
    ((code layout coefficientDefault initial default P comparison correct update updateBuffers reserve port draw).lower port).descriptionWords ≤
      codeBudget layout drawWords updateWords := by
  have prepared := (prepare_bounded layout coefficientDefault initial).code_le
  have folded := RowFold.code_bound layout.rows default P comparison correct update updateBuffers reserve port layout.capacity draw drawBound updateBound
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega
end Signatures.Runtime.CaliperBackend.TokenEvaluation
