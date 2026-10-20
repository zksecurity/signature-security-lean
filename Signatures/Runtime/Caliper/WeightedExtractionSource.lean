import Signatures.Runtime.Caliper.WeightedExtraction
import Signatures.Runtime.Caliper.WeightedTokenFoldSource
import Signatures.LinearFunctional.Proofs.LazyAGMTransport

/-! The complete generated transcript evaluator is the original scaled signing
extraction, including its ordered private cache. Index encoding is a proof
relation on encountered entries, never a runtime enumeration. -/
namespace Signatures.Runtime.CaliperBackend.WeightedExtraction
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction (privateListOracle)
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

theorem cache_growth (source : OracleComp spec layout.rows.accumulation.cache.value.Value)
    (value : layout.input.Value) (admitted : layout.ready value) (answer : layout.rows.state.Value)
    (reached : answer ∈ support (denote layout coefficientDefault zero initial default generator
      P comparison correct update updateBuffers reserve source value)) :
    answer.val.2.length ≤ value.val.2.length + layout.terms * value.val.1.1.length := by
  have growth := WeightedTokenFold.cache_growth layout.rows zero layout.terms layout.termCountFits layout.termStorageFits
    generator default P comparison correct update updateBuffers reserve source (foldValue layout coefficientDefault initial value)
    (foldValue_ready layout coefficientDefault initial value admitted) answer reached
  rw [foldValue_length] at growth
  exact growth

theorem remaining_room (source : OracleComp spec layout.rows.accumulation.cache.value.Value)
    (value : layout.input.Value) (remaining : Nat)
    (reserved : value.val.2.length + layout.terms * value.val.1.1.length + remaining ≤ layout.rows.accumulation.cache.capacityPred + 1)
    (answer : layout.rows.state.Value)
    (reached : answer ∈ support (denote layout coefficientDefault zero initial default generator
      P comparison correct update updateBuffers reserve source value)) :
    answer.val.2.length + remaining ≤ layout.rows.accumulation.cache.capacityPred + 1 := by
  have admitted : layout.ready value := by unfold Layouts.ready; omega
  have growth := cache_growth layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve
    source value admitted answer reached
  omega

section Source
variable [Semiring F] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [Module F (val.Value base)]
    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : zero.val = 0) (coefficientLaw : coefficientDefault.val = 0)
    (source : ProbComp layout.rows.accumulation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include combineLaw zeroLaw coefficientLaw uniform in
theorem denote_source (value : layout.input.Value) (admitted : layout.ready value) :
    Subtype.val <$> denote layout coefficientDefault zero initial default generator P comparison correct
      update updateBuffers reserve source value =
      (fun answer => (initial.val + answer.1, answer.2)) <$>
        (simulateQ privateListOracle
          (evalTerms (WeightedReduction.signedTerms generate value.val.1.2 value.val.1.1.reverse))).run value.val.2 := by
  have folded := WeightedTokenFold.listCache layout.rows zero layout.terms layout.termCountFits layout.termStorageFits
    generator default P comparison correct update updateBuffers reserve combineLaw zeroLaw source uniform
    (foldValue layout coefficientDefault initial value) (foldValue_ready layout coefficientDefault initial value admitted)
  rw [foldValue_rows] at folded
  change _ = WeightedAGM.Batching.cached generate
    (value.val.1.1.reverse.mapIdx (fun n token => (token, (value.val.1.2[n]?).getD coefficientDefault.val)))
    (initial.val, value.val.2) at folded
  rw [coefficientLaw] at folded
  exact folded.trans (WeightedAGM.Batching.cached_signedTerms generate value.val.1.1 value.val.1.2 (initial.val, value.val.2))

include combineLaw zeroLaw coefficientLaw uniform in
theorem denote_encoded {J : Type} [DecidableEq J] (encode : J → key.Value base)
    (injective : Function.Injective encode) (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map encode id))
    (value : layout.input.Value) (admitted : layout.ready value) (cache : List (J × val.Value base))
    (cacheEqual : value.val.2 = cache.map (Prod.map encode id)) :
    Subtype.val <$> denote layout coefficientDefault zero initial default generator P comparison correct
      update updateBuffers reserve source value =
      (fun answer => (initial.val + answer.1, answer.2.map (Prod.map encode id))) <$>
        (simulateQ privateListOracle
          (evalTerms (WeightedReduction.signedTerms sourceTerms value.val.1.2 value.val.1.1.reverse))).run cache := by
  have termsMapped : WeightedReduction.signedTerms generate value.val.1.2 value.val.1.1.reverse =
      (WeightedReduction.signedTerms sourceTerms value.val.1.2 value.val.1.1.reverse).map (Prod.map encode id) := by
    simpa only [Prod.map_id, List.map_id] using
      WeightedTransport.signedTerms_map encode id generate sourceTerms termsEqual value.val.1.2 value.val.1.1.reverse
  rw [denote_source layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve
    combineLaw zeroLaw coefficientLaw source uniform value admitted, termsMapped, cacheEqual,
    WeightedAGM.evalTerms_encoded encode injective, Functor.map_map]

include combineLaw zeroLaw coefficientLaw uniform in
theorem denote_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map keys id))
    (value : layout.input.Value) (admitted : layout.ready value) :
    (fun answer => (answer.val.1, answer.val.2.map (Prod.map keys.symm id))) <$>
      denote layout coefficientDefault zero initial default generator P comparison correct
        update updateBuffers reserve source value =
      (fun answer => (initial.val + answer.1, answer.2)) <$>
        (simulateQ privateListOracle
          (evalTerms (WeightedReduction.signedTerms sourceTerms value.val.1.2 value.val.1.1.reverse))).run
          (value.val.2.map (Prod.map keys.symm id)) := by
  have back : (value.val.2.map (Prod.map keys.symm id)).map (Prod.map keys id) = value.val.2 := by
    simp [List.map_map, Function.comp_def, Prod.map]
  have result := denote_encoded layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve
    combineLaw zeroLaw coefficientLaw source uniform keys keys.injective sourceTerms termsEqual value admitted
    (value.val.2.map (Prod.map keys.symm id)) back.symm
  calc
    _ = (fun answer => (answer.1, answer.2.map (Prod.map keys.symm id))) <$>
        (Subtype.val <$> denote layout coefficientDefault zero initial default generator P comparison correct
          update updateBuffers reserve source value) := by rw [Functor.map_map]
    _ = _ := by
      rw [result, Functor.map_map]
      simp [List.map_map, Function.comp_def, Prod.map]

include combineLaw zeroLaw coefficientLaw uniform in
theorem observe_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map keys id))
    (port : Interactive.Port w unifSpec) (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) draw)
    (tape : RandomTape w) (value : layout.input.Value) (admitted : layout.ready value)
    (before : State w) (holds : layout.input.representation.Holds value before) :
    (fun result => (fun answer => (answer.val.1, answer.val.2.map (Prod.map keys.symm id))) <$>
        Interactive.observe layout.rows.state.representation result) <$>
      (code layout coefficientDefault zero initial default generator P comparison correct
        update updateBuffers reserve port draw).execute port .unit tape before =
      some <$> ((fun answer => (initial.val + answer.1, answer.2)) <$>
        (simulateQ privateListOracle
          (evalTerms (WeightedReduction.signedTerms sourceTerms value.val.1.2 value.val.1.1.reverse))).run
          (value.val.2.map (Prod.map keys.symm id))) := by
  have observed := (refines layout coefficientDefault zero initial default generator P comparison correct
    update updateBuffers reserve port drawCorrect).observe tape value admitted before holds
  have mapped := congrArg (fun computation : ProbComp (Option layout.rows.state.Value) =>
    (fun result => (fun answer => (answer.val.1, answer.val.2.map (Prod.map keys.symm id))) <$> result) <$> computation) observed
  rw [← denote_equiv layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve
    combineLaw zeroLaw coefficientLaw source uniform keys sourceTerms termsEqual value admitted]
  simp only [Functor.map_map] at mapped ⊢
  exact mapped
end Source
end Signatures.Runtime.CaliperBackend.WeightedExtraction
