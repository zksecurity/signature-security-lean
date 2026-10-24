import Proofs.Runtime.Caliper.RowRequestNames
import Proofs.Runtime.Caliper.CacheAccumulateOracle
import Proofs.Runtime.Caliper.InteractiveFoldMemory

/-! One executed row evaluation, including request construction, lazy private
lookup and the accumulator update. The reservation counts actual remaining
rows; it does not reserve the entire allocated row buffer a second time. -/
namespace Signatures.Runtime.CaliperBackend.RowEvaluation
open Caliper BoundedSource OracleComp OracleSpec

section Frame
variable {w : Nat} {K G F R : Type} (layout : RowRequest.Layouts w K G F R)
abbrev Packet := layout.row.Value × layout.state.Value
def input : Representation w (Packet layout) :=
  layout.row.representation.prod layout.state.representation layout.raw.representation.fits
def ready (value : Packet layout) : Prop := layout.ready (value.1.val, value.2.val)
instance (value : Packet layout) : Decidable (ready layout value) := inferInstanceAs (Decidable (layout.ready _))
def room (remaining : Nat) (value : layout.state.Value) : Prop :=
  value.val.2.length + remaining ≤ layout.accumulation.cache.capacityPred + 1
theorem ready_of_room (remaining : Nat) (value : Packet layout) (valid : room layout (remaining + 1) value.2) :
    ready layout value := by
  change value.2.val.2.length ≤ _
  dsimp only [room] at valid
  omega
def admitted (value : {value : Packet layout // ready layout value}) : layout.input.Value :=
  ⟨(value.val.1.val, value.val.2.val), ⟨value.val.1.property, value.val.2.property⟩, value.property⟩
variable [DecidableEq K] (default : layout.accumulation.cache.value.Value)
def request (value : Packet layout) (valid : ready layout value) : layout.accumulation.input.Value :=
  ⟨((value.1.val.1.1, default.val, value.2.val.2, ()), value.1.val.2, value.2.val.1),
    (RowRequest.prepare layout default).preserves (admitted layout ⟨value, valid⟩).val (admitted layout ⟨value, valid⟩).property⟩
def prepareService : Realizer .unit ((input layout).restrict (ready layout)) layout.accumulation.input.representation
    (fun value => request layout default value.val value.property) :=
  (RowRequest.prepare layout default).program.viewInput _ (admitted layout) (fun _ => rfl)
end Frame

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

def code (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (RowRequest.prepare layout default).program.code)
    (EncodedCacheAccumulate.code layout.accumulation P comparison correct update updateBuffers reserve port draw)

/-- The arbitrary extension outside `ready` has no execution contract. The
loop proves readiness before every executed request. -/
def denote (source : OracleComp spec layout.accumulation.cache.value.Value) (value : Packet layout) :
    OracleComp spec layout.state.Value :=
  if valid : ready layout value then
    EncodedCacheAccumulate.denote layout.accumulation P comparison correct update updateBuffers reserve source
      (request layout default value valid)
  else pure value.2

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.accumulation.cache.value.Value}
    {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.accumulation.cache.lookup.unit.representation
      layout.accumulation.cache.value.representation (fun _ => source) draw)

include drawCorrect in
theorem refines : Interactive.RefinesOn (ready layout) port .unit (input layout) layout.state.representation
    (denote layout default P comparison correct update updateBuffers reserve source)
    (code layout default P comparison correct update updateBuffers reserve port draw) := by
  have prepared := Interactive.Refines.compute port .unit (prepareService layout default)
  have read := EncodedCacheAccumulate.refines layout.accumulation P comparison correct update updateBuffers reserve port source draw drawCorrect
  have composed := prepared.seq read
  intro tape value valid before holds
  unfold denote
  rw [dite_eq_left valid]
  simpa only [pure_bind, code, prepareService, Realizer.viewInput] using
    composed tape ⟨value, valid⟩ before holds

theorem preserves (remaining : Nat) (value : Packet layout) (valid : room layout (remaining + 1) value.2)
    (answer : layout.state.Value)
    (reached : answer ∈ support (denote layout default P comparison correct update updateBuffers reserve source value)) :
    room layout remaining answer := by
  have ready := ready_of_room layout remaining value valid
  unfold denote at reached
  rw [dite_eq_left ready] at reached
  have growth := EncodedCacheAccumulate.cache_growth layout.accumulation P comparison correct update updateBuffers reserve
    source (request layout default value ready) answer reached
  change answer.val.2.length ≤ value.2.val.2.length + 1 at growth
  dsimp only [room] at valid ⊢
  omega

theorem listCache (value : Packet layout) (valid : ready layout value) :
    Subtype.val <$> denote layout default P comparison correct update updateBuffers reserve source value =
      (fun result => (combine (value.1.val.2, result.1, value.2.val.1), result.2)) <$>
        (QueryImpl.ListCache.handler (fun _ => Subtype.val <$> source) value.1.val.1.1).run value.2.val.2 := by
  unfold denote
  rw [dite_eq_left valid]
  exact EncodedCacheAccumulate.listCache layout.accumulation P comparison correct update updateBuffers reserve source (request layout default value valid)

end Signatures.Runtime.CaliperBackend.RowEvaluation
