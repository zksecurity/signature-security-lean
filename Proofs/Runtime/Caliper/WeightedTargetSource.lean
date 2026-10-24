import Proofs.Runtime.Caliper.WeightedTarget

/-! The final-target program implements the source weighted private-oracle
evaluation followed by local scalar arithmetic. The identities preserve the
entire cache, including when its represented keys differ from source keys. -/
namespace Signatures.Runtime.CaliperBackend.WeightedTarget
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM WeightedCoefficient
open BLS.LazyAGM.Reduction (privateListOracle)

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F : Type}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
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
    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : zero.val = 0)
    (source : ProbComp layout.evaluation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include combineLaw zeroLaw uniform in
theorem denote_source (value : layout.input.Value) (admitted : valid layout (generate := generate) value) :
    Subtype.val <$> denote layout zero capacity countFits storageFits generator default P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve source value =
      (fun answer => (calculate (value.val.2.1, answer.1, value.val.2.2.1), answer.2)) <$>
        (simulateQ privateListOracle (evalTerms (generate value.val.1))).run value.val.2.2.2 := by
  have evaluated := GeneratedWeighted.evalTerms_source layout.evaluation layout.message capacity countFits storageFits
    generator default P comparison correct update updateBuffers reserve combineLaw source uniform
    (argument layout zero value) admitted
  have mapped := congrArg (fun computation : ProbComp (val.Value base × List (key.Value base × val.Value base)) =>
    (fun answer => (calculate (value.val.2.1, answer.1, value.val.2.2.1), answer.2)) <$> computation) evaluated
  simp only [Functor.map_map] at mapped
  simp only [argument, zeroLaw, zero_add] at mapped
  simp only [denote, evaluationSource, Functor.map_map, completed, EncodedCacheScalarResult.completed,
    postValue, productView, saved, argument, zeroLaw]
  exact mapped

include combineLaw zeroLaw uniform in
theorem denote_encoded {J : Type} [DecidableEq J] (encode : J → key.Value base)
    (injective : Function.Injective encode) (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map encode id))
    (value : layout.input.Value) (admitted : valid layout (generate := generate) value)
    (cache : List (J × val.Value base)) (cacheEqual : value.val.2.2.2 = cache.map (Prod.map encode id)) :
    Subtype.val <$> denote layout zero capacity countFits storageFits generator default P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve source value =
      (fun answer => (calculate (value.val.2.1, answer.1, value.val.2.2.1), answer.2.map (Prod.map encode id))) <$>
        (simulateQ privateListOracle (evalTerms (sourceTerms value.val.1))).run cache := by
  rw [denote_source layout zero capacity countFits storageFits generator default P comparison correct
    update updateBuffers reserve extract extractBuffers extractReserve combineLaw zeroLaw source uniform value admitted,
    termsEqual, cacheEqual, WeightedAGM.evalTerms_encoded encode injective, Functor.map_map]

include combineLaw zeroLaw uniform in
theorem denote_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map keys id))
    (value : layout.input.Value) (admitted : valid layout (generate := generate) value) :
    (fun answer => (answer.val.1, answer.val.2.map (Prod.map keys.symm id))) <$>
      denote layout zero capacity countFits storageFits generator default P comparison correct
        update updateBuffers reserve extract extractBuffers extractReserve source value =
      (fun answer => (calculate (value.val.2.1, answer.1, value.val.2.2.1), answer.2)) <$>
        (simulateQ privateListOracle (evalTerms (sourceTerms value.val.1))).run
          (value.val.2.2.2.map (Prod.map keys.symm id)) := by
  have back : (value.val.2.2.2.map (Prod.map keys.symm id)).map (Prod.map keys id) = value.val.2.2.2 := by
    simp [List.map_map, Function.comp_def, Prod.map]
  have result := denote_encoded layout zero capacity countFits storageFits generator default P comparison correct
    update updateBuffers reserve extract extractBuffers extractReserve combineLaw zeroLaw source uniform
    keys keys.injective sourceTerms termsEqual value admitted (value.val.2.2.2.map (Prod.map keys.symm id)) back.symm
  calc
    _ = (fun answer => (answer.1, answer.2.map (Prod.map keys.symm id))) <$>
        (Subtype.val <$> denote layout zero capacity countFits storageFits generator default P comparison correct
          update updateBuffers reserve extract extractBuffers extractReserve source value) := by rw [Functor.map_map]
    _ = _ := by
      rw [result, Functor.map_map]
      simp [List.map_map, Function.comp_def, Prod.map]

include combineLaw zeroLaw uniform in
theorem observe_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map keys id))
    (port : Interactive.Port w unifSpec) (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines port .unit layout.evaluation.cache.lookup.unit.representation
      layout.evaluation.cache.value.representation (fun _ => source) draw)
    (tape : RandomTape w) (value : layout.input.Value) (admitted : valid layout (generate := generate) value)
    (before : State w) (holds : layout.input.representation.Holds value before) :
    (fun result => (fun answer => (answer.val.1, answer.val.2.map (Prod.map keys.symm id))) <$>
        Interactive.observe (output layout).representation result) <$>
      (code layout zero capacity countFits storageFits generator default P comparison correct update updateBuffers reserve
        extract extractBuffers extractReserve port draw).execute port .unit tape before =
      some <$> ((fun answer => (calculate (value.val.2.1, answer.1, value.val.2.2.1), answer.2)) <$>
        (simulateQ privateListOracle (evalTerms (sourceTerms value.val.1))).run
          (value.val.2.2.2.map (Prod.map keys.symm id))) := by
  have observed := (refines layout zero capacity countFits storageFits generator default P comparison correct
    update updateBuffers reserve extract extractBuffers extractReserve port draw drawCorrect).observe
    tape value admitted before holds
  have mapped := congrArg (fun computation : ProbComp (Option (output layout).Value) =>
    (fun result => (fun answer => (answer.val.1, answer.val.2.map (Prod.map keys.symm id))) <$> result) <$> computation) observed
  rw [← denote_equiv layout zero capacity countFits storageFits generator default P comparison correct
    update updateBuffers reserve extract extractBuffers extractReserve combineLaw zeroLaw source uniform
    keys sourceTerms termsEqual value admitted]
  simp only [Functor.map_map] at mapped ⊢
  exact mapped

end Signatures.Runtime.CaliperBackend.WeightedTarget
