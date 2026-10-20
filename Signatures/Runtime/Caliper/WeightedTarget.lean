import Signatures.Runtime.Caliper.WeightedCoefficient
import Signatures.Runtime.Caliper.CacheScalarResult

/-! Evaluate the forged message from zero using the existing private cache,
then execute the local extraction arithmetic. The numerator and signing
contribution are retained by actual copying. Pair-valued private evaluations
still produce a scalar result, together with the complete cache. -/
namespace Signatures.Runtime.CaliperBackend.WeightedTarget
open Caliper BoundedSource OracleComp OracleSpec WeightedCoefficient

abbrev output {w : Nat} {K M F R : Type} (layout : Layouts w K M F R) :=
  CacheScalarResult.output layout.evaluation

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) M F (val.Value base))
    (zero : layout.evaluation.cache.value.Value)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term layout.evaluation).representation.encoding.words +
      layout.state.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.message
      (GeneratedWeighted.terms layout.evaluation capacity countFits storageFits) generate)
    (default : layout.evaluation.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.evaluation.combine layout.evaluation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {calculate : F × (val.Value base × val.Value base) → F}
    (extract : Implementation .unit layout.evaluation.combine layout.evaluation.coefficient calculate)
    {extractSlots : Nat} (extractBuffers : extract.program.code.memBound ≤ extractSlots)
    (extractReserve : extractSlots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec) (draw : Interactive.Code w)

def completed (value : layout.state.Value × layout.evaluation.saved.Value) : (output layout).Value :=
  EncodedCacheScalarResult.completed layout.evaluation extract extractBuffers extractReserve (postValue layout value)
def tail : Realizer .unit
    (layout.state.representation.prod layout.evaluation.saved.representation layout.post.representation.fits)
    (output layout).representation (completed layout extract extractBuffers extractReserve) :=
  (CacheScalarResult.finish layout.evaluation extract extractBuffers extractReserve).program.viewInput _
    (postValue layout) (by
      intro value
      exact congrArg (layout.state.representation.prod layout.evaluation.saved.representation
        layout.post.representation.fits).encoding.encode
        ((productView layout.state layout.evaluation.saved).apply_symm_apply value))
def code : Interactive.Code w :=
  .seq (.compute (prepare layout zero).code)
    (.seq (evaluate layout capacity countFits storageFits generator default P comparison correct
      update updateBuffers reserve port draw)
      (.compute (tail layout extract extractBuffers extractReserve).code))
def denote (source : OracleComp spec layout.evaluation.cache.value.Value) (value : layout.input.Value) :
    OracleComp spec (output layout).Value :=
  (fun answer => completed layout extract extractBuffers extractReserve (answer, saved layout value)) <$>
    evaluationSource layout capacity countFits storageFits generator default P comparison correct
      update updateBuffers reserve source (argument layout zero value)

variable {source : OracleComp spec layout.evaluation.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.evaluation.cache.lookup.unit.representation
      layout.evaluation.cache.value.representation (fun _ => source) draw)

include drawCorrect in
theorem refines :
    Interactive.RefinesOn (valid layout (generate := generate)) port .unit layout.input.representation
      (output layout).representation
      (denote layout zero capacity countFits storageFits generator default P comparison correct
        update updateBuffers reserve extract extractBuffers extractReserve source)
      (code layout zero capacity countFits storageFits generator default P comparison correct
        update updateBuffers reserve extract extractBuffers extractReserve port draw) := by
  have evaluated := (GeneratedWeighted.refines layout.evaluation layout.message capacity countFits storageFits generator
    port layout.evaluationInput.fits default P comparison correct update updateBuffers reserve drawCorrect).retain
    (by decide) layout.evaluation.saved.representation layout.evaluation.cache.wordFits
    layout.prepared.fits layout.post.representation.fits
  have ended := evaluated.seq
    ((Interactive.Refines.compute port .unit (tail layout extract extractBuffers extractReserve)).on (fun _ => True))
    (fun _ _ _ _ => trivial)
  have composed := ((Interactive.Refines.compute port .unit (prepare layout zero)).on
    (valid layout (generate := generate))).seq ended (by
      intro value admitted answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact admitted)
  convert composed using 1
  · funext value
    simp only [pure_bind, bind_pure_comp, Functor.map_map, denote, evaluationSource]
    rfl
  · rfl

theorem cache_growth (source : OracleComp spec layout.evaluation.cache.value.Value)
    (value : layout.input.Value) (admitted : valid layout (generate := generate) value)
    (answer : (output layout).Value)
    (reached : answer ∈ support (denote layout zero capacity countFits storageFits generator
      default P comparison correct update updateBuffers reserve extract extractBuffers extractReserve source value)) :
    answer.val.2.length ≤ value.val.2.2.2.length + (generate value.val.1).length := by
  simp only [denote, support_map, Set.mem_image] at reached
  obtain ⟨result, supported, rfl⟩ := reached
  exact GeneratedWeighted.cache_growth layout.evaluation layout.message capacity countFits storageFits generator
    default P comparison correct update updateBuffers reserve source (argument layout zero value) admitted result supported

end Signatures.Runtime.CaliperBackend.WeightedTarget
