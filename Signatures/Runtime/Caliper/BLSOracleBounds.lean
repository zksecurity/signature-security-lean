import Signatures.Runtime.Caliper.BLSOracleSource
import Signatures.Runtime.Caliper.TagBounds

/-! The full service charges its runtime tags, all stored branches, random
forwarding, reply padding and copies of the private store. -/

namespace Signatures.Runtime.CaliperBackend.BLSOracle
open Caliper BoundedSource OracleComp OracleSpec

section Widths
variable {w : Nat} {M R C G : Type} [DecidableEq M]
    (layout : BLSReply.Layouts w M R C G) (default : layout.cache.value.Value)
    (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)

theorem widths : (randomInput layout randomBound randomFits).encoding.words ≤ width layout ∧
    (BLSDispatch.input layout default).representation.encoding.words ≤ width layout ∧
    (output layout randomBound randomFits).encoding.words ≤ width layout := by
  have store := store_le layout
  have group := group_output_le layout
  have left := layout.input_le default.val false
  have right := layout.input_le default.val true
  change 1 + layout.store.representation.encoding.words ≤ layout.width + 3 ∧
    1 + max (layout.input default.val false).representation.encoding.words (layout.input default.val true).representation.encoding.words ≤ layout.width + 3 ∧
    1 + max (2 + layout.store.representation.encoding.words) layout.output.representation.encoding.words ≤ layout.width + 3
  omega

def timeBudget (groupTime : Nat) : Nat := max (34 + 12 * width layout) groupTime + 16 * width layout + 2
def codeBudget (groupWords : Nat) : Nat := groupWords + 143 * width layout + 232
end Widths

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
    {drawSource : ProbComp layout.cache.value.Value}
    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
      layout.cache.lookup.unit.representation layout.cache.value.representation (fun _ => drawSource) draw)
    {drawTime drawWords : Nat} {responseTime responseWords : Bool → Nat}
    (drawTimeBound : Interactive.TimeBound (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
      layout.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower (UniformQuery.port randomBound layout.cache.wordFits randomFits)).descriptionWords ≤ drawWords)
    (responseBound : ∀ signing, (response signing).BoundedBy (responseTime signing) (responseWords signing))

include drawCorrect drawTimeBound responseBound in
theorem time_bound : Interactive.TimeBound (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
    (input layout default randomBound randomFits)
    (code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw)
    (timeBudget layout (BLSDispatch.timeBudget layout drawTime responseTime)) := by
  have rt := Interactive.TimeBound.compute (port := UniformQuery.port randomBound layout.cache.wordFits randomFits) (cost := .unit)
    (randomTag layout randomBound randomFits) _ (inl_time _ _ _ _)
  have gt := Interactive.TimeBound.compute (port := UniformQuery.port randomBound layout.cache.wordFits randomFits) (cost := .unit)
    (groupTag layout randomBound randomFits) _ (inr_time _ _ _ _)
  have random := (UniformQuery.forward_time randomBound layout.cache.wordFits randomFits layout.store.representation (storageFits layout)).seq
    (UniformQuery.forward_refines randomBound layout.cache.wordFits randomFits layout.store.representation (storageFits layout)) rt
  have group := (BLSDispatch.time_bound layout default P comparison correct _ draw response responseBuffers reserve drawCorrect drawTimeBound responseBound).seq
    (BLSDispatch.refines layout default P comparison correct _ draw response responseBuffers reserve drawSource drawCorrect) gt
  have dispatched := Interactive.TimeBound.dispatch _ _ random group (width_pos layout.cache.wordFits) (inputFits layout default randomBound randomFits)
  apply dispatched.mono
  rw [Interactive.dispatchTime_unit]
  have bound := widths layout default randomBound randomFits
  have store := store_le layout
  change 2 + max
    (8 * (randomInput layout randomBound randomFits).encoding.words +
      (34 + 12 * layout.store.representation.encoding.words + 8 * (output layout randomBound randomFits).encoding.words))
    (8 * (BLSDispatch.input layout default).representation.encoding.words +
      (BLSDispatch.timeBudget layout drawTime responseTime + 8 * (output layout randomBound randomFits).encoding.words)) ≤ _
  dsimp only [timeBudget, width] at bound ⊢
  omega

include drawWordsBound responseBound in
theorem code_bound : ((code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw).lower
    (UniformQuery.port randomBound layout.cache.wordFits randomFits)).descriptionWords ≤
      codeBudget layout (BLSDispatch.codeBudget layout drawWords responseWords) := by
  have random := UniformQuery.forward_words randomBound layout.cache.wordFits randomFits layout.store.representation
  have group := BLSDispatch.code_bound layout default P comparison correct _ draw response responseBuffers reserve drawWordsBound responseBound
  have rt := inl_words (randomOutput layout randomBound randomFits) layout.output.representation layout.cache.wordFits (outputFits layout randomBound randomFits)
  have gt := inr_words (randomOutput layout randomBound randomFits) layout.output.representation layout.cache.wordFits (outputFits layout randomBound randomFits)
  have bound := widths layout default randomBound randomFits
  have store := store_le layout
  rw [code, Interactive.dispatch_descriptionWords]
  simp only [randomCode, groupCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  change _ ∧ _ ∧ 1 + max (randomOutput layout randomBound randomFits).encoding.words layout.output.representation.encoding.words ≤ width layout at bound
  change descriptionWords (randomTag layout randomBound randomFits).code ≤ _ at rt
  change descriptionWords (groupTag layout randomBound randomFits).code ≤ _ at gt
  dsimp only [codeBudget, width] at bound ⊢
  omega

theorem names {drawSlots responseSlots : Nat}
    (drawNames : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound layout.cache.wordFits randomFits)) drawSlots)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseSlots) :
    WordIO.NamesAccounted ((code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw).lower
      (UniformQuery.port randomBound layout.cache.wordFits randomFits)) (max (max 5 drawSlots) responseSlots) := by
  have rt := (WordIO.NamesAccounted.compute (inl_names (randomOutput layout randomBound randomFits) layout.output.representation
    layout.cache.wordFits (outputFits layout randomBound randomFits)).accounted).mono (show 3 ≤ max (max 5 drawSlots) responseSlots by omega)
  have gt := (WordIO.NamesAccounted.compute (inr_names (randomOutput layout randomBound randomFits) layout.output.representation
    layout.cache.wordFits (outputFits layout randomBound randomFits)).accounted).mono (show 3 ≤ max (max 5 drawSlots) responseSlots by omega)
  have random := (UniformQuery.forward_names randomBound layout.cache.wordFits randomFits layout.store.representation).accounted.mono
    (show 3 ≤ max (max 5 drawSlots) responseSlots by omega)
  have group := BLSDispatch.names layout default P comparison correct _ draw response responseBuffers reserve drawNames responseNames
  apply Interactive.dispatch_names (UniformQuery.port randomBound layout.cache.wordFits randomFits)
    (left := randomCode layout randomBound randomFits)
    (right := groupCode layout default randomBound randomFits P comparison correct response responseBuffers reserve draw)
  · exact random.seq rt
  · exact group.seq gt

theorem descriptionFits {drawSlots : Nat}
    (drawFits : (draw.lower (UniformQuery.port randomBound layout.cache.wordFits randomFits)).DescriptionFits)
    (drawNames : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound layout.cache.wordFits randomFits)) drawSlots)
    (drawReserve : drawSlots + 1 < 2 ^ w) :
    ((code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw).lower
      (UniformQuery.port randomBound layout.cache.wordFits randomFits)).DescriptionFits :=
  Interactive.dispatch_descriptionFits _ _ _ _ _ layout.cache.wordFits
    (.seq layout.cache.wordFits (UniformQuery.forward_descriptionFits randomBound layout.cache.wordFits randomFits layout.store.representation (storageFits layout))
      (.compute (randomTag layout randomBound randomFits).description_fits))
    (.seq layout.cache.wordFits (BLSDispatch.descriptionFits layout default P comparison correct _ draw response responseBuffers reserve drawFits drawNames drawReserve)
      (.compute (groupTag layout randomBound randomFits).description_fits))
    (randomInput layout randomBound randomFits).fits (BLSDispatch.input layout default).representation.fits

end Signatures.Runtime.CaliperBackend.BLSOracle
