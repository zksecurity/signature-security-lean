import Proofs.Runtime.Caliper.WeightedExtractionPrepareBounds

/-! One actual transcript evaluator: chronological row construction, encoded
initial accumulator, and the private-cache fold. Capacity is reserved for the
number of stored tokens, regardless of missing or surplus coefficients. -/
namespace Signatures.Runtime.CaliperBackend.WeightedExtraction
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M G F : Type}
    [DecidableEq (key.Value base)] (layout : Layouts w (key.Value base) M G F (val.Value base))
    (coefficientDefault : layout.rows.accumulation.coefficient.Value)
    (zero initial default : layout.rows.accumulation.cache.value.Value)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.rows.weighted.message
      (GeneratedWeighted.terms layout.rows.accumulation layout.terms layout.termCountFits layout.termStorageFits) generate)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.rows.accumulation.combine layout.rows.accumulation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I}

def code (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (prepare layout coefficientDefault initial).program.code)
    (WeightedTokenFold.code layout.rows zero layout.terms layout.termCountFits layout.termStorageFits generator default P comparison correct update updateBuffers reserve layout.capacity port draw)
def denote (source : OracleComp spec layout.rows.accumulation.cache.value.Value) (value : layout.input.Value) : OracleComp spec layout.rows.state.Value :=
  WeightedTokenFold.denote layout.rows zero layout.terms layout.termCountFits layout.termStorageFits generator default P comparison correct update updateBuffers reserve source (foldValue layout coefficientDefault initial value)
omit [DecidableEq (key.Value base)] in
theorem foldValue_ready (value : layout.input.Value) (ready : layout.ready value) :
    WeightedTokenFold.valid (base := base) (key := key) (val := val) layout.rows layout.terms (foldValue layout coefficientDefault initial value) := by
  unfold WeightedTokenFold.valid WeightedToken.room
  rw [foldValue_length]
  exact ready

def preparedProgram : Realizer .unit layout.input.representation
    (WeightedTokenFold.input layout.rows layout.capacity layout.countFits layout.foldFits) (foldValue layout coefficientDefault initial) :=
  (prepare layout coefficientDefault initial).program.viewOutput _ (foldValue layout coefficientDefault initial)
    (fun value => foldView_bytes layout (preparedValue layout coefficientDefault initial value))

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.rows.accumulation.cache.value.Value}
    {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) draw)
include drawCorrect in
theorem refines : Interactive.RefinesOn layout.ready port .unit layout.input.representation layout.rows.state.representation
    (denote layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve source)
    (code layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port draw) := by
  have first := (Interactive.Refines.compute port .unit (preparedProgram layout coefficientDefault initial)).on layout.ready
  have second := WeightedTokenFold.refines layout.rows zero layout.terms layout.termCountFits layout.termStorageFits generator default P comparison correct update updateBuffers reserve port drawCorrect
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

def timeBudget (generatorTime drawTime updateTime : Nat) : Nat :=
  prepareTime layout + WeightedTokenFold.timeBudget layout.rows layout.terms layout.termCountFits layout.termStorageFits layout.capacity generatorTime drawTime updateTime
def codeBudget (generatorWords drawWords updateWords : Nat) : Nat :=
  prepareWords layout + WeightedTokenFold.codeBudget layout.rows layout.terms layout.termCountFits layout.termStorageFits layout.capacity generatorWords drawWords updateWords + 2

include drawCorrect in
theorem time_bound {generatorTime generatorWords drawTime updateTime updateWords : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawBound : Interactive.TimeBound port .unit layout.rows.accumulation.cache.lookup.unit.representation draw drawTime)
    (updateBound : update.BoundedBy updateTime updateWords) :
    Interactive.TimeBoundOn layout.ready port .unit layout.input.representation
      (code layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port draw)
      (timeBudget layout generatorTime drawTime updateTime) := by
  have first := (Interactive.Refines.compute port .unit (preparedProgram layout coefficientDefault initial)).on layout.ready
  have firstBound := (Interactive.TimeBound.compute (port := port) (cost := .unit)
    (preparedProgram layout coefficientDefault initial) _ (prepare_bounded layout coefficientDefault initial).time_le).on layout.ready
  exact Interactive.TimeBoundOn.seq first firstBound
    (WeightedTokenFold.time_bound layout.rows zero layout.terms layout.termCountFits layout.termStorageFits generator default P comparison correct update updateBuffers reserve port drawCorrect
      layout.capacity layout.countFits layout.foldFits generatorBound drawBound updateBound) (by
        intro value valid answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact foldValue_ready layout coefficientDefault initial value valid)

theorem code_bound (draw : Interactive.Code w) {generatorTime generatorWords drawWords updateTime updateWords : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawBound : (draw.lower port).descriptionWords ≤ drawWords) (updateBound : update.BoundedBy updateTime updateWords) :
    ((code layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port draw).lower port).descriptionWords ≤
      codeBudget layout generatorWords drawWords updateWords := by
  have prepared := (prepare_bounded layout coefficientDefault initial).code_le
  have folded := WeightedTokenFold.code_bound layout.rows zero layout.terms layout.termCountFits layout.termStorageFits generator default P comparison correct update updateBuffers reserve port layout.capacity draw generatorBound drawBound updateBound
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega
end Signatures.Runtime.CaliperBackend.WeightedExtraction
