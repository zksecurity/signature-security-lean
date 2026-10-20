import Signatures.Runtime.Caliper.WeightedSignatureTail

/-! Erasing the composed tail recovers chronological signed-term extraction,
then target evaluation against exactly the returned private cache. Key transport
and the actual execution observation preserve this full joint result. -/
namespace Signatures.Runtime.CaliperBackend.WeightedSignatureTail
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction (privateListOracle)

noncomputable def sourceProgram {w : Nat} {K J M G F R : Type} [DecidableEq J]
    [Semiring F] [SampleableType R] [AddCommMonoid R] [Module F R]
    (layout : WeightedExtraction.Layouts w K M G F R) (terms : M → List (J × F))
    (calculate : F × (R × R) → F) (value : Input layout) (cache : List (J × R)) :
    ProbComp (F × List (J × R)) := do
  let signatures ← (simulateQ privateListOracle
    (evalTerms (WeightedReduction.signedTerms terms value.1.val.1.2 value.1.val.1.1.reverse))).run cache
  (fun target => (calculate (value.2.val.2, target.1, signatures.1), target.2)) <$>
    (simulateQ privateListOracle (evalTerms (terms value.2.val.1))).run signatures.2

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M G F : Type}
    [DecidableEq (key.Value base)] [Semiring F] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [Module F (val.Value base)]
    (layout : WeightedExtraction.Layouts w (key.Value base) M G F (val.Value base))
    (coefficientDefault : layout.rows.accumulation.coefficient.Value)
    (zero default : layout.rows.accumulation.cache.value.Value)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.rows.weighted.message
      (GeneratedWeighted.terms layout.rows.accumulation layout.terms layout.termCountFits layout.termStorageFits) generate)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.rows.accumulation.combine layout.rows.accumulation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {calculate : F × (val.Value base × val.Value base) → F}
    (extract : Implementation .unit layout.rows.accumulation.combine layout.rows.accumulation.coefficient calculate)
    {extractSlots : Nat} (extractBuffers : extract.program.code.memBound ≤ extractSlots)
    (extractReserve : extractSlots + 2 < 2 ^ w)
    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : zero.val = 0) (coefficientLaw : coefficientDefault.val = 0)
    (source : ProbComp layout.rows.accumulation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include combineLaw zeroLaw uniform in
theorem finish_source (value : Returned layout) (admitted : finalReady layout (generate := generate) value) :
    Subtype.val <$> finish layout zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve source value =
      (fun target => (calculate (value.2.val.2, target.1, value.1.val.1), target.2)) <$>
        (simulateQ privateListOracle (evalTerms (generate value.2.val.1))).run value.1.val.2 :=
  WeightedTarget.denote_source layout.rows.weighted zero layout.terms layout.termCountFits layout.termStorageFits
    generator default P comparison correct update updateBuffers reserve extract extractBuffers extractReserve
    combineLaw zeroLaw source uniform (argument layout value) admitted

include combineLaw zeroLaw coefficientLaw uniform in
theorem denote_source (value : Input layout) (admitted : ready layout value) :
    Subtype.val <$> denote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve source value =
      sourceProgram layout generate calculate value value.1.val.2 := by
  have evaluated := WeightedExtraction.denote_source layout coefficientDefault zero zero default generator
    P comparison correct update updateBuffers reserve combineLaw zeroLaw coefficientLaw source uniform
    value.1 (signing_ready layout value admitted)
  simp only [zeroLaw, zero_add, Prod.mk.eta, id_map'] at evaluated
  unfold sourceProgram
  rw [← evaluated, bind_map_left]
  simp only [denote, evaluation, bind_map_left, map_bind]
  apply bind_congr_of_forall_mem_support
  intro result reached
  have preserved := preserves layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    value admitted (result, value.2) (by
      simpa only [evaluation, support_map, Set.mem_image] using ⟨result, reached, rfl⟩)
  exact finish_source layout zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve combineLaw zeroLaw source uniform (result, value.2) preserved

include combineLaw zeroLaw coefficientLaw uniform in
theorem denote_encoded {J : Type} [DecidableEq J] (encode : J → key.Value base)
    (injective : Function.Injective encode) (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map encode id))
    (value : Input layout) (admitted : ready layout value) (cache : List (J × val.Value base))
    (cacheEqual : value.1.val.2 = cache.map (Prod.map encode id)) :
    Subtype.val <$> denote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve source value =
      (fun answer => (answer.1, answer.2.map (Prod.map encode id))) <$>
        sourceProgram layout sourceTerms calculate value cache := by
  have termsMapped : WeightedReduction.signedTerms generate value.1.val.1.2 value.1.val.1.1.reverse =
      (WeightedReduction.signedTerms sourceTerms value.1.val.1.2 value.1.val.1.1.reverse).map (Prod.map encode id) := by
    simpa only [Prod.map_id, List.map_id] using
      WeightedTransport.signedTerms_map encode id generate sourceTerms termsEqual value.1.val.1.2 value.1.val.1.1.reverse
  rw [denote_source layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve combineLaw zeroLaw coefficientLaw source uniform value admitted]
  unfold sourceProgram
  rw [termsMapped, cacheEqual, WeightedAGM.evalTerms_encoded encode injective, bind_map_left, map_bind]
  apply bind_congr_of_forall_mem_support
  intro signatures _
  rw [termsEqual, WeightedAGM.evalTerms_encoded encode injective, Functor.map_map, Functor.map_map]

include combineLaw zeroLaw coefficientLaw uniform in
theorem denote_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map keys id))
    (value : Input layout) (admitted : ready layout value) :
    (fun answer => (answer.val.1, answer.val.2.map (Prod.map keys.symm id))) <$>
      denote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
        extract extractBuffers extractReserve source value =
      sourceProgram layout sourceTerms calculate value (value.1.val.2.map (Prod.map keys.symm id)) := by
  have back : (value.1.val.2.map (Prod.map keys.symm id)).map (Prod.map keys id) = value.1.val.2 := by
    simp [List.map_map, Function.comp_def, Prod.map]
  have result := denote_encoded layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve combineLaw zeroLaw coefficientLaw source uniform
    keys keys.injective sourceTerms termsEqual value admitted (value.1.val.2.map (Prod.map keys.symm id)) back.symm
  calc
    _ = (fun answer => (answer.1, answer.2.map (Prod.map keys.symm id))) <$>
        (Subtype.val <$> denote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
          extract extractBuffers extractReserve source value) := by rw [Functor.map_map]
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
    (tape : RandomTape w) (value : Input layout) (admitted : ready layout value)
    (before : State w) (holds : (input layout).Holds value before) :
    (fun result => (fun answer => (answer.val.1, answer.val.2.map (Prod.map keys.symm id))) <$>
        Interactive.observe (output layout).representation result) <$>
      (code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
        extract extractBuffers extractReserve port draw).execute port .unit tape before =
      some <$> sourceProgram layout sourceTerms calculate value (value.1.val.2.map (Prod.map keys.symm id)) := by
  have observed := (refines layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve port drawCorrect).observe tape value admitted before holds
  have mapped := congrArg (fun computation : ProbComp (Option (output layout).Value) =>
    (fun result => (fun answer => (answer.val.1, answer.val.2.map (Prod.map keys.symm id))) <$> result) <$> computation) observed
  rw [← denote_equiv layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve combineLaw zeroLaw coefficientLaw source uniform keys sourceTerms termsEqual value admitted]
  simp only [Functor.map_map] at mapped ⊢
  exact mapped

end Signatures.Runtime.CaliperBackend.WeightedSignatureTail
