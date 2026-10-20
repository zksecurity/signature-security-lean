import Signatures.Runtime.Caliper.WeightedCoefficientRouting
import Signatures.Runtime.WeightedBatching

/-! One weighted transcript occurrence: generate and evaluate its original
terms from zero, retain its extraction coefficient and old accumulator, then
run the existing local accumulator update. All cache reads remain present. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCoefficient
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction (privateListOracle)

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
    {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec) (draw : Interactive.Code w)

def valid (value : layout.input.Value) : Prop :=
  value.val.2.2.2.length + (generate value.val.1).length ≤ layout.evaluation.cache.capacityPred + 1
def evaluator := GeneratedWeighted.code layout.evaluation layout.message capacity countFits storageFits generator
  port default P comparison correct update updateBuffers reserve draw
def evaluate : Interactive.Code w :=
  Interactive.retain (evaluator layout capacity countFits storageFits generator default P comparison correct
    update updateBuffers reserve port draw)
    (Interactive.savedBuffer port (evaluator layout capacity countFits storageFits generator default P comparison correct
      update updateBuffers reserve port draw))
    layout.evaluationInput.encoding.words layout.state.representation.encoding.words
    layout.evaluation.saved.representation.encoding.words
def evaluationSource (source : OracleComp spec layout.evaluation.cache.value.Value) :=
  GeneratedWeighted.denote layout.evaluation layout.message capacity countFits storageFits generator
    default P comparison correct update updateBuffers reserve source
def postValue (value : layout.state.Value × layout.evaluation.saved.Value) : layout.post.Value :=
  (productView layout.state layout.evaluation.saved).symm value
def completed (value : layout.state.Value × layout.evaluation.saved.Value) : layout.state.Value :=
  EncodedCacheAccumulate.completed layout.evaluation update updateBuffers reserve (postValue layout value)
def tail : Realizer .unit
    (layout.state.representation.prod layout.evaluation.saved.representation layout.post.representation.fits)
    layout.state.representation (completed layout update updateBuffers reserve) :=
  (CacheAccumulate.finish layout.evaluation update updateBuffers reserve).program.viewInput _
    (postValue layout) (by
      intro value
      exact congrArg (layout.state.representation.prod layout.evaluation.saved.representation
        layout.post.representation.fits).encoding.encode
        ((productView layout.state layout.evaluation.saved).apply_symm_apply value))
def code : Interactive.Code w :=
  .seq (.compute (prepare layout zero).code)
    (.seq (evaluate layout capacity countFits storageFits generator default P comparison correct
      update updateBuffers reserve port draw)
      (.compute (tail layout update updateBuffers reserve).code))
def denote (source : OracleComp spec layout.evaluation.cache.value.Value) (value : layout.input.Value) :
    OracleComp spec layout.state.Value :=
  (fun answer => completed layout update updateBuffers reserve (answer, saved layout value)) <$>
    evaluationSource layout capacity countFits storageFits generator default P comparison correct
      update updateBuffers reserve source (argument layout zero value)

variable {source : OracleComp spec layout.evaluation.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.evaluation.cache.lookup.unit.representation
      layout.evaluation.cache.value.representation (fun _ => source) draw)

include drawCorrect in
theorem refines :
    Interactive.RefinesOn (valid layout (generate := generate)) port .unit layout.input.representation
      layout.state.representation
      (denote layout zero capacity countFits storageFits generator default P comparison correct
        update updateBuffers reserve source)
      (code layout zero capacity countFits storageFits generator default P comparison correct
        update updateBuffers reserve port draw) := by
  have evaluated := (GeneratedWeighted.refines layout.evaluation layout.message capacity countFits storageFits generator
    port layout.evaluationInput.fits default P comparison correct update updateBuffers reserve drawCorrect).retain
    (by decide) layout.evaluation.saved.representation layout.evaluation.cache.wordFits
    layout.prepared.fits layout.post.representation.fits
  have ended := evaluated.seq
    ((Interactive.Refines.compute port .unit (tail layout update updateBuffers reserve)).on (fun _ => True))
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
    (answer : layout.state.Value)
    (reached : answer ∈ support (denote layout zero capacity countFits storageFits generator
      default P comparison correct update updateBuffers reserve source value)) :
    answer.val.2.length ≤ value.val.2.2.2.length + (generate value.val.1).length := by
  simp only [denote, support_map, Set.mem_image] at reached
  obtain ⟨result, supported, rfl⟩ := reached
  exact GeneratedWeighted.cache_growth layout.evaluation layout.message capacity countFits storageFits generator
    default P comparison correct update updateBuffers reserve source (argument layout zero value) admitted result supported

section Source
variable [Semiring F] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [Module F (val.Value base)]
    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : zero.val = 0)

include combineLaw zeroLaw in
theorem denote_source (source : ProbComp layout.evaluation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (value : layout.input.Value) (admitted : valid layout (generate := generate) value) :
    Subtype.val <$> denote layout zero capacity countFits storageFits generator default P comparison correct
      update updateBuffers reserve source value =
      (fun answer => (value.val.2.2.1 + answer.1, answer.2)) <$>
        (simulateQ privateListOracle
          (evalTerms ((generate value.val.1).map fun term => (term.1, value.val.2.1 * term.2)))).run
          value.val.2.2.2 := by
  have evaluated := GeneratedWeighted.evalTerms_source layout.evaluation layout.message capacity countFits storageFits
    generator default P comparison correct update updateBuffers reserve combineLaw source uniform
    (argument layout zero value) admitted
  have mapped := congrArg (fun computation : ProbComp (val.Value base × List (key.Value base × val.Value base)) =>
    (fun answer => (combine (value.val.2.1, answer.1, value.val.2.2.1), answer.2)) <$> computation) evaluated
  rw [WeightedAGM.Batching.evalTerms_scale, simulateQ_map, StateT.run_map]
  simp only [denote, evaluationSource, Functor.map_map] at mapped ⊢
  simp only [argument, zeroLaw, zero_add, combineLaw] at mapped
  simp only [completed, EncodedCacheAccumulate.completed, postValue, productView,
    saved, argument, zeroLaw, combineLaw]
  exact mapped

end Source
end Signatures.Runtime.CaliperBackend.WeightedCoefficient
