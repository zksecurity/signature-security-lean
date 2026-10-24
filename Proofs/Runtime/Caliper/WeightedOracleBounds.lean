import Proofs.Runtime.Caliper.WeightedOracleSource
import Proofs.Runtime.Caliper.TagBounds

/-! Complete weighted service costs. Runtime selects one branch; stored code
includes all branches, tags, payload normalization and copied private state. -/
namespace Signatures.Runtime.CaliperBackend.WeightedOracle
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F C G : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) M F (val.Value base) C G)
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


def groupTime (generatorTime drawTime updateTime : Nat) (responseTime : Bool → Nat) : Nat :=
  2 + max
    (8 * layout.hashing.input.representation.encoding.words + WeightedHash.timeBudget layout.hashing drawTime (responseTime false))
    (8 * layout.signing.input.representation.encoding.words +
      WeightedSign.timeBudget layout.signing capacity countFits storageFits generatorTime drawTime updateTime (responseTime true))
def groupWords (generatorWords drawWords updateWords : Nat) (responseWords : Bool → Nat) : Nat :=
  WeightedHash.codeBudget layout.hashing drawWords (responseWords false) +
    WeightedSign.codeBudget layout.signing capacity countFits storageFits generatorWords drawWords updateWords (responseWords true) +
    26 * layout.hashing.input.representation.encoding.words + 26 * layout.signing.input.representation.encoding.words + 40

def timeBudget (generatorTime drawTime updateTime : Nat) (responseTime : Bool → Nat) : Nat :=
  2 + max
    (8 * (layout.randomInput randomBound randomFits).encoding.words +
      (34 + 12 * layout.store.representation.encoding.words + 8 * (layout.output randomBound randomFits).encoding.words))
    (8 * layout.groupInput.encoding.words +
      (groupTime layout capacity countFits storageFits generatorTime drawTime updateTime responseTime +
        8 * (layout.output randomBound randomFits).encoding.words))
def codeBudget (generatorWords drawWords updateWords : Nat) (responseWords : Bool → Nat) : Nat :=
  (160 + 39 * layout.store.representation.encoding.words) +
    groupWords layout capacity countFits storageFits generatorWords drawWords updateWords responseWords +
    52 * (layout.output randomBound randomFits).encoding.words + 32 +
    26 * (layout.randomInput randomBound randomFits).encoding.words + 26 * layout.groupInput.encoding.words + 40

variable {source : ProbComp layout.evaluation.cache.value.Value}
    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
      layout.evaluation.cache.lookup.unit.representation layout.evaluation.cache.value.representation (fun _ => source) draw)
    {generatorTime generatorWords drawTime drawWords updateTime updateWords : Nat} {responseTime responseWords : Bool → Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawTimeBound : Interactive.TimeBound (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
      layout.evaluation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)).descriptionWords ≤ drawWords)
    (updateBound : update.BoundedBy updateTime updateWords)
    (responseBound : ∀ signing, (response signing).BoundedBy (responseTime signing) (responseWords signing))

include drawCorrect generatorBound drawTimeBound updateBound responseBound in
theorem group_time : Interactive.TimeBoundOn (groupValid layout (generate := generate))
    (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit layout.groupInput
    (groupCode layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve)
    (groupTime layout capacity countFits storageFits generatorTime drawTime updateTime responseTime) := by
  have hashed := WeightedHash.time_bound layout.hashing P comparison correct _ draw (response false) (responseBuffers false)
    responseReserve drawCorrect drawTimeBound (responseBound false)
  have signed := WeightedSign.time_bound layout.signing layout.zero capacity countFits storageFits generator layout.default
    P comparison correct update updateBuffers updateReserve _ draw (response true) (responseBuffers true) responseReserve
    drawCorrect generatorBound drawTimeBound updateBound (responseBound true)
  have bounded := Interactive.TimeBoundOn.dispatch _ _ (hashed.on (fun _ => True)) signed
    (width_pos layout.evaluation.cache.wordFits) layout.groupInput.fits
  rw [Interactive.dispatchTime_unit] at bounded
  exact bounded

include generatorBound drawWordsBound updateBound responseBound in
theorem group_words : ((groupCode layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve).lower
        (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)).descriptionWords ≤
    groupWords layout capacity countFits storageFits generatorWords drawWords updateWords responseWords := by
  have hashed := WeightedHash.code_bound layout.hashing P comparison correct _ draw (response false) (responseBuffers false)
    responseReserve drawWordsBound (responseBound false)
  have signed := WeightedSign.code_bound layout.signing layout.zero capacity countFits storageFits generator layout.default
    P comparison correct update updateBuffers updateReserve _ draw (response true) (responseBuffers true) responseReserve
    generatorBound drawWordsBound updateBound (responseBound true)
  rw [groupCode, Interactive.dispatch_descriptionWords]
  change ((hashCode layout randomBound randomFits P comparison correct draw response responseBuffers responseReserve).lower _).descriptionWords ≤ _ at hashed
  change ((signCode layout capacity countFits storageFits generator randomBound randomFits P comparison correct
    update updateBuffers updateReserve draw response responseBuffers responseReserve).lower _).descriptionWords ≤ _ at signed
  unfold groupWords
  omega

include drawCorrect generatorBound drawTimeBound updateBound responseBound in
theorem time_bound : Interactive.TimeBoundOn (valid layout (generate := generate) randomBound)
    (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit (layout.input randomBound randomFits)
    (code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve)
    (timeBudget layout capacity countFits storageFits randomBound randomFits generatorTime drawTime updateTime responseTime) := by
  have randomTagTime := Interactive.TimeBound.compute (port := UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)
    (cost := .unit) (layout.randomTag randomBound randomFits) _ (inl_time _ _ _ _)
  have groupTagTime := Interactive.TimeBound.compute (port := UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)
    (cost := .unit) (layout.groupTag randomBound randomFits) _ (inr_time _ _ _ _)
  have random := (UniformQuery.forward_time randomBound layout.evaluation.cache.wordFits randomFits layout.store.representation
    (layout.randomOutput randomBound randomFits).fits).seq
      (UniformQuery.forward_refines randomBound layout.evaluation.cache.wordFits randomFits layout.store.representation
        (layout.randomOutput randomBound randomFits).fits) randomTagTime
  have group := (group_time layout capacity countFits storageFits generator randomBound randomFits P comparison correct
    update updateBuffers updateReserve draw response responseBuffers responseReserve drawCorrect
    generatorBound drawTimeBound updateBound responseBound).seq
      (group_refines layout capacity countFits storageFits generator randomBound randomFits P comparison correct
        update updateBuffers updateReserve draw response responseBuffers responseReserve drawCorrect)
      (groupTagTime.on (fun _ => True)) (fun _ _ _ _ => trivial)
  have bounded := Interactive.TimeBoundOn.dispatch _ _ (random.on (fun _ => True)) group
    (width_pos layout.evaluation.cache.wordFits) (layout.input randomBound randomFits).fits
  rw [Interactive.dispatchTime_unit] at bounded
  exact bounded

include generatorBound drawWordsBound updateBound responseBound in
theorem code_bound : ((code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve).lower
        (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)).descriptionWords ≤
    codeBudget layout capacity countFits storageFits randomBound randomFits generatorWords drawWords updateWords responseWords := by
  have random := UniformQuery.forward_words randomBound layout.evaluation.cache.wordFits randomFits layout.store.representation
  have group := group_words layout capacity countFits storageFits generator randomBound randomFits P comparison correct
    update updateBuffers updateReserve draw response responseBuffers responseReserve generatorBound drawWordsBound updateBound responseBound
  have leftTag := inl_words (layout.randomOutput randomBound randomFits) layout.groupOutput.representation
    layout.evaluation.cache.wordFits (layout.output randomBound randomFits).fits
  have rightTag := inr_words (layout.randomOutput randomBound randomFits) layout.groupOutput.representation
    layout.evaluation.cache.wordFits (layout.output randomBound randomFits).fits
  change descriptionWords (layout.randomTag randomBound randomFits).code ≤
    26 * (layout.output randomBound randomFits).encoding.words + 14 at leftTag
  change descriptionWords (layout.groupTag randomBound randomFits).code ≤
    26 * (layout.output randomBound randomFits).encoding.words + 14 at rightTag
  rw [code, Interactive.dispatch_descriptionWords]
  simp only [randomCode, taggedGroup, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

end Signatures.Runtime.CaliperBackend.WeightedOracle
