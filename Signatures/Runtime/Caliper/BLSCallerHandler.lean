import Signatures.Runtime.Caliper.BLSCallerPacketBounds
import Signatures.Runtime.Caliper.BLSOracleBounds
import Signatures.Runtime.Caliper.InteractiveInvariantBounds

/-! The BLS service in the generic caller's request/store and reply/store
interface. The code constructs the request, runs the existing complete service,
and reconstructs the reply. Correctness is proved on the ready domain; no
completed handler implementation or resource contract is assumed. -/

namespace Signatures.Runtime.CaliperBackend.BLSCallerHandler
open Caliper BoundedSource OracleComp OracleSpec BLSCallerPackets

section Preparation
variable {w : Nat} {M R C G : Type} [DecidableEq M]
    (layout : BLSReply.Layouts w M R C G) (default : layout.cache.value.Value)
    (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)

def admitted : Representation w {value : Packet layout randomBound // ready layout default randomBound value} :=
  (input layout randomBound randomFits).restrict (ready layout default randomBound)

/-- Same instructions as `prepare`; the ready-domain proof supplies only the
service's subtype packaging, whose bytes are already constructed by the code. -/
def prepareService : Realizer .unit (admitted layout default randomBound randomFits)
    (BLSOracle.input layout default randomBound randomFits)
    (fun value => serviceRequest layout default randomBound value.val value.property) :=
  ((prepare layout randomBound randomFits).viewInput (admitted layout default randomBound randomFits) Subtype.val
    (fun _ => rfl)).viewOutput (BLSOracle.input layout default randomBound randomFits)
      (fun value => serviceRequest layout default randomBound value.val value.property)
      (fun value => request_bytes layout default randomBound randomFits value.val value.property)

end Preparation

variable {w : Nat} {C G : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)]
    (layout : BLSReply.Layouts w (key.Value base) (val.Value base) C G)
    (default : layout.cache.value.Value) (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.responseInput layout.point (respond signing))
    {slots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w) (draw : Interactive.Code w)

def code : Interactive.Code w :=
  .seq (.compute (prepare layout randomBound randomFits).code)
    (.seq (BLSOracle.code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw)
      (.compute (finish layout randomBound randomFits).code))

/-- A total mathematical extension of the source on the ready domain. The
unready branch makes no specification claim about the executed code and is
never used by the caller's reservation invariant. -/
def denote (drawSource : ProbComp layout.cache.value.Value) (value : Packet layout randomBound) :
    ProbComp (Reply layout randomBound × layout.store.Value) :=
  if valid : ready layout default randomBound value then
    finished layout randomBound <$>
      BLSOracle.denote layout default randomBound P comparison correct response responseBuffers reserve drawSource
        (serviceRequest layout default randomBound value valid)
  else pure (.inl ⟨⟨0, by omega⟩, ⟨0, Nat.succ_pos _⟩⟩, value.2)

variable {drawSource : ProbComp layout.cache.value.Value}
    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
      layout.cache.lookup.unit.representation layout.cache.value.representation (fun _ => drawSource) draw)

include drawCorrect in
theorem refines : Interactive.RefinesOn (ready layout default randomBound)
    (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
    (input layout randomBound randomFits) (output layout randomBound randomFits)
    (denote layout default randomBound P comparison correct response responseBuffers reserve drawSource)
    (code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw) := by
  have prepared := Interactive.Refines.compute (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
    (prepareService layout default randomBound randomFits)
  have service := BLSOracle.refines layout default randomBound randomFits P comparison correct response responseBuffers reserve draw drawSource drawCorrect
  have converted := Interactive.Refines.compute (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
    (finish layout randomBound randomFits)
  have composed := prepared.seq (service.seq converted)
  intro tape value valid before holds
  have checked := composed tape ⟨value, valid⟩ before holds
  simpa only [denote, dite_eq_left valid, pure_bind, bind_pure_comp, code, prepareService,
    Realizer.viewInput, Realizer.viewOutput] using checked

include drawCorrect in
theorem time {drawTime : Nat} {responseTime responseWords : Bool → Nat}
    (drawTimeBound : Interactive.TimeBound (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
      layout.cache.lookup.unit.representation draw drawTime)
    (responseBound : ∀ signing, (response signing).BoundedBy (responseTime signing) (responseWords signing)) :
    Interactive.TimeBoundOn (ready layout default randomBound)
      (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit (input layout randomBound randomFits)
      (code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw)
      (BLSOracle.timeBudget layout (BLSDispatch.timeBudget layout drawTime responseTime) + 108 * width layout + 8) := by
  have prepared := Interactive.Refines.compute (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
    (prepareService layout default randomBound randomFits)
  have service := BLSOracle.refines layout default randomBound randomFits P comparison correct response responseBuffers reserve draw drawSource drawCorrect
  have preparedTime := Interactive.TimeBound.compute (port := UniformQuery.port randomBound layout.cache.wordFits randomFits)
    (cost := .unit) (prepareService layout default randomBound randomFits) (64 * width layout + 6)
    (fun value => prepare_time layout randomBound randomFits value.val)
  have serviceTime := BLSOracle.time_bound layout default randomBound randomFits P comparison correct response responseBuffers reserve
    draw drawCorrect drawTimeBound responseBound
  have convertedTime := Interactive.TimeBound.compute (port := UniformQuery.port randomBound layout.cache.wordFits randomFits)
    (cost := .unit) (finish layout randomBound randomFits) (44 * width layout + 2) (finish_time layout randomBound randomFits)
  have composed := (preparedTime.seq prepared (serviceTime.seq service convertedTime)).mono
    (larger := BLSOracle.timeBudget layout (BLSDispatch.timeBudget layout drawTime responseTime) + 108 * width layout + 8) (by omega)
  intro tape value valid before holds finished reached
  exact composed tape ⟨value, valid⟩ before holds finished reached

theorem words {drawWords : Nat} {responseTime responseWords : Bool → Nat}
    (drawBound : (draw.lower (UniformQuery.port randomBound layout.cache.wordFits randomFits)).descriptionWords ≤ drawWords)
    (responseBound : ∀ signing, (response signing).BoundedBy (responseTime signing) (responseWords signing)) :
    ((code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw).lower
      (UniformQuery.port randomBound layout.cache.wordFits randomFits)).descriptionWords ≤
        BLSOracle.codeBudget layout (BLSDispatch.codeBudget layout drawWords responseWords) + 710 * width layout + 420 := by
  have prepared := prepare_words layout randomBound randomFits
  have converted := finish_words layout randomBound randomFits
  have service := BLSOracle.code_bound layout default randomBound randomFits P comparison correct response responseBuffers reserve draw drawBound responseBound
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega

theorem names {drawSlots responseSlots : Nat}
    (drawNames : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound layout.cache.wordFits randomFits)) drawSlots)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseSlots) :
    WordIO.NamesAccounted ((code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw).lower
      (UniformQuery.port randomBound layout.cache.wordFits randomFits)) (max (max 5 drawSlots) responseSlots) :=
  ((WordIO.NamesAccounted.compute (prepare_names layout randomBound randomFits)).mono (by omega)).seq
    ((BLSOracle.names layout default randomBound randomFits P comparison correct response responseBuffers reserve draw drawNames responseNames).seq
      ((WordIO.NamesAccounted.compute (finish_names layout randomBound randomFits)).mono (by omega)))

theorem descriptionFits {drawSlots : Nat}
    (drawFits : (draw.lower (UniformQuery.port randomBound layout.cache.wordFits randomFits)).DescriptionFits)
    (drawNames : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound layout.cache.wordFits randomFits)) drawSlots)
    (drawReserve : drawSlots + 1 < 2 ^ w) :
    ((code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw).lower
      (UniformQuery.port randomBound layout.cache.wordFits randomFits)).DescriptionFits :=
  .seq layout.cache.wordFits (.compute (prepare layout randomBound randomFits).description_fits)
    (.seq layout.cache.wordFits
      (BLSOracle.descriptionFits layout default randomBound randomFits P comparison correct response responseBuffers reserve draw drawFits drawNames drawReserve)
      (.compute (finish layout randomBound randomFits).description_fits))

end Signatures.Runtime.CaliperBackend.BLSCallerHandler
