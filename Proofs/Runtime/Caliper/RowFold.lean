import Proofs.Runtime.Caliper.RowEvaluationBounds

/-! The actual bounded row evaluator. Its body is constructed from request
copies, the lazy cache and a local accumulator update. No whole-loop contract
is supplied. Stored unrolling and copying are included in the bounds. -/
namespace Signatures.Runtime.CaliperBackend.RowFold
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G F : Type}
    [DecidableEq (key.Value base)] (layout : RowRequest.Layouts w (key.Value base) G F (val.Value base))
    (default : layout.accumulation.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.accumulation.combine layout.accumulation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I}

abbrev Input (capacity : Nat) := BoundedList layout.row.Value capacity × layout.state.Value
def input (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * layout.row.representation.encoding.words + layout.state.representation.encoding.words < 2 ^ w) :
    Representation w (Input layout capacity) :=
  InteractiveFold.frame layout.row.representation layout.state.representation capacity countFits storageFits
def valid {capacity : Nat} (value : Input layout capacity) : Prop :=
  RowEvaluation.room layout value.1.val.length value.2
def code (capacity : Nat) (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  let body := RowEvaluation.code layout default P comparison correct update updateBuffers reserve port draw
  InteractiveFold.code body (Interactive.savedBuffer port body)
    layout.row.representation.encoding.words layout.state.representation.encoding.words capacity
def denote (source : OracleComp spec layout.accumulation.cache.value.Value) {capacity : Nat}
    (value : Input layout capacity) : OracleComp spec layout.state.Value :=
  InteractiveFold.denote (RowEvaluation.denote layout default P comparison correct update updateBuffers reserve source) value
def timeBudget (capacity drawTime updateTime : Nat) : Nat :=
  InteractiveFold.timeBudget layout.row.representation.encoding.words layout.state.representation.encoding.words capacity
    (RowEvaluation.timeBudget layout drawTime updateTime)
def codeBudget (capacity drawWords updateWords : Nat) : Nat :=
  InteractiveFold.codeBudget layout.row.representation.encoding.words layout.state.representation.encoding.words capacity
    (RowEvaluation.codeBudget layout drawWords updateWords)

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.accumulation.cache.value.Value}
    {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.accumulation.cache.lookup.unit.representation
      layout.accumulation.cache.value.representation (fun _ => source) draw)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * layout.row.representation.encoding.words + layout.state.representation.encoding.words < 2 ^ w)

include drawCorrect in
theorem refines : Interactive.RefinesOn (valid layout) port .unit (input layout capacity countFits storageFits) layout.state.representation
    (denote layout default P comparison correct update updateBuffers reserve source)
    (code layout default P comparison correct update updateBuffers reserve capacity port draw) :=
  InteractiveFold.refines layout.row.representation layout.state.representation layout.accumulation.cache.wordFits
    layout.raw.representation.fits port (RowEvaluation.room layout)
    (fun remaining tape value valid before holds =>
      RowEvaluation.refines layout default P comparison correct update updateBuffers reserve port drawCorrect
        tape value (RowEvaluation.ready_of_room layout remaining value valid) before holds)
    (RowEvaluation.preserves layout default P comparison correct update updateBuffers reserve) capacity countFits storageFits

include drawCorrect in
theorem time_bound {drawTime updateTime updateWords : Nat}
    (drawBound : Interactive.TimeBound port .unit layout.accumulation.cache.lookup.unit.representation draw drawTime)
    (updateBound : update.BoundedBy updateTime updateWords) :
    Interactive.TimeBoundOn (valid layout) port .unit (input layout capacity countFits storageFits)
      (code layout default P comparison correct update updateBuffers reserve capacity port draw)
      (timeBudget layout capacity drawTime updateTime) :=
  InteractiveFold.time_bound layout.row.representation layout.state.representation layout.accumulation.cache.wordFits
    layout.raw.representation.fits port (RowEvaluation.room layout)
    (fun remaining tape value valid before holds =>
      RowEvaluation.refines layout default P comparison correct update updateBuffers reserve port drawCorrect
        tape value (RowEvaluation.ready_of_room layout remaining value valid) before holds)
    (RowEvaluation.preserves layout default P comparison correct update updateBuffers reserve)
    (fun remaining tape value valid before holds finished reached =>
      RowEvaluation.time_bound layout default P comparison correct update updateBuffers reserve port drawCorrect drawBound updateBound
        tape value (RowEvaluation.ready_of_room layout remaining value valid) before holds finished reached)
    capacity countFits storageFits

theorem code_bound (draw : Interactive.Code w) {drawWords updateTime updateWords : Nat}
    (drawBound : (draw.lower port).descriptionWords ≤ drawWords) (updateBound : update.BoundedBy updateTime updateWords) :
    ((code layout default P comparison correct update updateBuffers reserve capacity port draw).lower port).descriptionWords ≤
      codeBudget layout capacity drawWords updateWords :=
  InteractiveFold.code_bound port _ _ _ capacity
    (RowEvaluation.code_bound layout default P comparison correct update updateBuffers reserve port draw drawBound updateBound)

theorem names (draw : Interactive.Code w) {drawNames updateNames : Nat}
    (drawBound : WordIO.NamesBound (draw.lower port) drawNames) (updateBound : NamesAccounted update.program.code updateNames) :
    WordIO.NamesAccounted ((code layout default P comparison correct update updateBuffers reserve capacity port draw).lower port)
      (max (max 5 drawNames) updateNames) :=
  InteractiveFold.names port _ _ _ capacity
    (RowEvaluation.names layout default P comparison correct update updateBuffers reserve port draw drawBound updateBound)

include countFits storageFits in
theorem descriptionFits (draw : Interactive.Code w) (drawFits : (draw.lower port).DescriptionFits) {drawNames : Nat}
    (drawBound : WordIO.NamesBound (draw.lower port) drawNames) (namesFit : drawNames + 2 < 2 ^ w) :
    ((code layout default P comparison correct update updateBuffers reserve capacity port draw).lower port).DescriptionFits := by
  have savedFit : Interactive.savedBuffer port (RowEvaluation.code layout default P comparison correct update updateBuffers reserve port draw) < 2 ^ w := by
    have bound := RowEvaluation.buffers layout default P comparison correct update updateBuffers reserve port draw
    have := drawBound.buffers
    have := layout.accumulation.cache.wordFits
    dsimp only [Interactive.savedBuffer]
    omega
  exact InteractiveFold.descriptionFits port _ layout.row.representation layout.state.representation
    layout.accumulation.cache.wordFits layout.raw.representation.fits
    (RowEvaluation.descriptionFits layout default P comparison correct update updateBuffers reserve port draw drawFits drawBound namesFit)
    savedFit capacity countFits storageFits

end Signatures.Runtime.CaliperBackend.RowFold
