import Proofs.Runtime.Caliper.WeightedCallerPacketBounds
import Proofs.Runtime.Caliper.WeightedOracleMemory

/-! Caller-facing weighted service: executed packet preparation, the constructed
oracle and executed reply conversion. All correctness and bounds are derived
from local components on the reachable readiness domain. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCallerHandler
open Caliper BoundedSource OracleComp OracleSpec WeightedCallerPackets

section Preparation
variable {w : Nat} {K M F R C G : Type} [DecidableEq K]
    (layout : WeightedOracle.Layouts w K M F R C G) (randomBound : Nat)
    (randomFits : randomBound + 1 ≤ 2 ^ w) (generate : M → List (K × F))

def admitted : Representation w {value : Packet layout randomBound // ready layout randomBound generate value} :=
  (input layout randomBound randomFits).restrict (ready layout randomBound generate)

def prepareService : Realizer .unit (admitted layout randomBound randomFits generate)
    (layout.input randomBound randomFits)
    (fun value => serviceRequest layout randomBound generate value.val value.property) :=
  ((prepare layout randomBound randomFits).viewInput (admitted layout randomBound randomFits generate) Subtype.val
    (fun _ => rfl)).viewOutput (layout.input randomBound randomFits)
      (fun value => serviceRequest layout randomBound generate value.val value.property)
      (fun value => request_bytes layout randomBound randomFits generate value.val value.property)
end Preparation

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F C G : Type}
    [DecidableEq (key.Value base)]
    (layout : WeightedOracle.Layouts w (key.Value base) M F (val.Value base) C G)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term layout.evaluation).representation.encoding.words +
      layout.signing.evaluated.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.message
      (GeneratedWeighted.terms layout.evaluation capacity countFits storageFits) generate)
    (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.evaluation.combine layout.evaluation.cache.value combine)
    {updateSlots : Nat} (updateBuffers : update.program.code.memBound ≤ updateSlots) (updateReserve : updateSlots + 2 < 2 ^ w)
    (draw : Interactive.Code w)
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.responseInput layout.point (respond signing))
    {responseSlots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ responseSlots)
    (responseReserve : responseSlots < 2 ^ w)

theorem request_valid (value : Packet layout randomBound) (accepted : ready layout randomBound generate value) :
    WeightedOracle.valid layout (generate := generate) randomBound
      (serviceRequest layout randomBound generate value accepted) := by
  rcases value with ⟨n | (index | message), saved⟩
  · trivial
  · trivial
  · exact accepted.2

def code : Interactive.Code w :=
  .seq (.compute (prepare layout randomBound randomFits).code)
    (.seq (WeightedOracle.code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve)
      (.compute (finish layout randomBound randomFits).code))

/-- The unready branch is a total mathematical extension, never used by a
reserved caller. No claim about target behavior is made outside readiness. -/
def denote (source : ProbComp layout.evaluation.cache.value.Value) (value : Packet layout randomBound) :
    ProbComp (Reply layout randomBound × layout.store.Value) :=
  if accepted : ready layout randomBound generate value then
    finished layout randomBound <$>
      WeightedOracle.denote layout capacity countFits storageFits generator randomBound P comparison correct
        update updateBuffers updateReserve response source (serviceRequest layout randomBound generate value accepted)
  else pure (.inl ⟨⟨0, Nat.zero_lt_succ _⟩, ⟨0, Nat.succ_pos _⟩⟩, value.2)

variable {source : ProbComp layout.evaluation.cache.value.Value}
    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
      layout.evaluation.cache.lookup.unit.representation layout.evaluation.cache.value.representation (fun _ => source) draw)

include drawCorrect in
theorem refines : Interactive.RefinesOn (ready layout randomBound generate)
    (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
    (input layout randomBound randomFits) (output layout randomBound randomFits)
    (denote layout capacity countFits storageFits generator randomBound P comparison correct
      update updateBuffers updateReserve response source)
    (code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve) := by
  have prepared := (Interactive.Refines.compute (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
    (prepareService layout randomBound randomFits generate)).on (fun _ => True)
  have service := WeightedOracle.refines layout capacity countFits storageFits generator randomBound randomFits P comparison correct
    update updateBuffers updateReserve draw response responseBuffers responseReserve drawCorrect
  have converted := (Interactive.Refines.compute (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
    (finish layout randomBound randomFits)).on (fun _ => True)
  have composed := prepared.seq (service.seq converted (fun _ _ _ _ => trivial)) (by
    intro value _ answer supported
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst answer
    exact request_valid layout randomBound value.val value.property)
  intro tape value accepted before holds
  have checked := composed tape ⟨value, accepted⟩ trivial before holds
  simpa only [denote, dite_eq_left accepted, pure_bind, bind_pure_comp, code, prepareService,
    Realizer.viewInput, Realizer.viewOutput] using checked

end Signatures.Runtime.CaliperBackend.WeightedCallerHandler
