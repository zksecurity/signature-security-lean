import Signatures.Runtime.Caliper.WeightedExtractor

/-! Source equality for the entire weighted extractor preserves the joint
scalar/cache result. Hash terms, signed terms and target terms are evaluated in
that order by the original private-list oracle. -/
namespace Signatures.Runtime.CaliperBackend.WeightedExtractor
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction (privateListOracle)

noncomputable def sourceProgram {w : Nat} {K J M G F R : Type} [DecidableEq J]
    [Semiring F] [SampleableType R] [AddCommMonoid R] [Module F R]
    (layout : Layouts w K M G F R) (terms : M → List (J × F))
    (numerator : F × R → F) (calculate : F × (R × R) → F)
    (value : layout.input.Value) (hashLog : List (J × G)) (cache : List (J × R)) :
    ProbComp (F × List (J × R)) := do
  let hashes ← (simulateQ privateListOracle
    (evalTerms (BLS.LazyAGM.Reduction.traceTerms value.val.1.2.2.1 hashLog.reverse))).run cache
  let signatures ← (simulateQ privateListOracle
    (evalTerms (WeightedReduction.signedTerms terms value.val.1.2.2.2 value.val.2.2.2.reverse))).run hashes.2
  (fun target => (calculate (numerator (value.val.1.2.1, hashes.1), target.1, signatures.1), target.2)) <$>
    (simulateQ privateListOracle (evalTerms (terms value.val.1.1))).run signatures.2

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M G F : Type}
    [DecidableEq (key.Value base)] [Semiring F] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [Module F (val.Value base)] (layout : Layouts w (key.Value base) M G F (val.Value base))
    (coefficientDefault : layout.signing.rows.accumulation.coefficient.Value)
    (zero default : layout.signing.rows.accumulation.cache.value.Value)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.signing.rows.weighted.message
      (GeneratedWeighted.terms layout.signing.rows.accumulation layout.signing.terms layout.signing.termCountFits layout.signing.termStorageFits) generate)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.signing.rows.accumulation.combine layout.signing.rows.accumulation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {calculate : F × (val.Value base × val.Value base) → F}
    (extract : Implementation .unit layout.signing.rows.accumulation.combine layout.signing.rows.accumulation.coefficient calculate)
    {extractSlots : Nat} (extractBuffers : extract.program.code.memBound ≤ extractSlots)
    (extractReserve : extractSlots + 2 < 2 ^ w)
    {numerator : F × val.Value base → F}
    (sum : Implementation .unit layout.numeratorInput layout.scalar numerator)
    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : zero.val = 0) (coefficientLaw : coefficientDefault.val = 0)
    (source : ProbComp layout.signing.rows.accumulation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include combineLaw zeroLaw coefficientLaw uniform in
theorem denote_source (value : layout.input.Value) (admitted : layout.ready value) :
    Subtype.val <$> denote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve sum source value =
      sourceProgram layout generate numerator calculate value value.val.2.2.1 value.val.2.1 := by
  have hashed := TokenEvaluation.evalTerms_source layout.hashes coefficientDefault zero default P comparison correct
    update updateBuffers reserve combineLaw coefficientLaw source uniform (layout.preparedValue value).1
    (layout.hash_evaluation_ready _ (layout.prepare_ready value admitted))
  simp only [zeroLaw, zero_add, Prod.mk.eta, id_map'] at hashed
  simp only [Layouts.preparedValue] at hashed
  unfold sourceProgram
  rw [← hashed, bind_map_left]
  simp only [denote, hashDenote, map_bind]
  erw [bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro result reached
  have room := TokenEvaluation.remaining_room layout.hashes coefficientDefault zero default P comparison correct
    update updateBuffers reserve source (layout.preparedValue value).1
    (layout.signing.terms * value.val.2.2.2.length + layout.signing.terms)
    (by simpa only [Layouts.ready, Layouts.preparedValue, Layouts.hashes, hashRows, Nat.add_assoc] using admitted) result reached
  have tailReady : WeightedSignatureTail.ready layout.signing
      (transitionValue layout sum (result, (layout.preparedValue value).2)) := by
    simpa only [RowEvaluation.room, Layouts.hashes, hashRows, WeightedSignatureTail.ready, transitionValue, Layouts.tailValue,
      Layouts.numeratorValue, Layouts.preparedValue, Nat.add_assoc] using room
  exact WeightedSignatureTail.denote_source layout.signing coefficientDefault zero default generator
    P comparison correct update updateBuffers reserve extract extractBuffers extractReserve
    combineLaw zeroLaw coefficientLaw source uniform _ tailReady

include combineLaw zeroLaw coefficientLaw uniform in
theorem bad_denote_source (value : layout.input.Value) (admitted : layout.badReady value) :
    Subtype.val <$> badDenote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve source value =
      WeightedSignatureTail.sourceProgram layout.signing generate calculate (layout.signatureValue value) value.val.2.1 :=
  WeightedSignatureTail.denote_source layout.signing coefficientDefault zero default generator
    P comparison correct update updateBuffers reserve extract extractBuffers extractReserve
    combineLaw zeroLaw coefficientLaw source uniform _ admitted

include combineLaw zeroLaw coefficientLaw uniform in
theorem denote_encoded {J : Type} [DecidableEq J] (encode : J → key.Value base)
    (injective : Function.Injective encode) (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map encode id))
    (value : layout.input.Value) (admitted : layout.ready value)
    (hashLog : List (J × G)) (cache : List (J × val.Value base))
    (hashEqual : value.val.2.2.1 = hashLog.map (Prod.map encode id))
    (cacheEqual : value.val.2.1 = cache.map (Prod.map encode id)) :
    Subtype.val <$> denote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve sum source value =
      (fun answer => (answer.1, answer.2.map (Prod.map encode id))) <$>
        sourceProgram layout sourceTerms numerator calculate value hashLog cache := by
  have termsMapped : WeightedReduction.signedTerms generate value.val.1.2.2.2 value.val.2.2.2.reverse =
      (WeightedReduction.signedTerms sourceTerms value.val.1.2.2.2 value.val.2.2.2.reverse).map (Prod.map encode id) := by
    simpa only [Prod.map_id, List.map_id] using
      WeightedTransport.signedTerms_map encode id generate sourceTerms termsEqual value.val.1.2.2.2 value.val.2.2.2.reverse
  rw [denote_source layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve sum combineLaw zeroLaw coefficientLaw source uniform value admitted]
  unfold sourceProgram
  rw [hashEqual, ← List.map_reverse, BLS.LazyAGM.MessageTransport.traceTerms_map, cacheEqual,
    WeightedAGM.evalTerms_encoded encode injective, bind_map_left, map_bind]
  apply bind_congr_of_forall_mem_support
  intro hashes _
  rw [termsMapped, WeightedAGM.evalTerms_encoded encode injective, bind_map_left, map_bind]
  apply bind_congr_of_forall_mem_support
  intro signatures _
  rw [termsEqual, WeightedAGM.evalTerms_encoded encode injective, Functor.map_map, Functor.map_map]

include combineLaw zeroLaw coefficientLaw uniform in
theorem denote_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map keys id))
    (value : layout.input.Value) (admitted : layout.ready value) :
    (fun answer => (answer.val.1, answer.val.2.map (Prod.map keys.symm id))) <$>
      denote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
        extract extractBuffers extractReserve sum source value =
      sourceProgram layout sourceTerms numerator calculate value
        (value.val.2.2.1.map (Prod.map keys.symm id)) (value.val.2.1.map (Prod.map keys.symm id)) := by
  have hashBack : (value.val.2.2.1.map (Prod.map keys.symm id)).map (Prod.map keys id) = value.val.2.2.1 := by
    simp [List.map_map, Function.comp_def, Prod.map]
  have cacheBack : (value.val.2.1.map (Prod.map keys.symm id)).map (Prod.map keys id) = value.val.2.1 := by
    simp [List.map_map, Function.comp_def, Prod.map]
  have result := denote_encoded layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve sum combineLaw zeroLaw coefficientLaw source uniform
    keys keys.injective sourceTerms termsEqual value admitted _ _ hashBack.symm cacheBack.symm
  calc
    _ = (fun answer => (answer.1, answer.2.map (Prod.map keys.symm id))) <$>
        (Subtype.val <$> denote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
          extract extractBuffers extractReserve sum source value) := by rw [Functor.map_map]
    _ = _ := by
      rw [result, Functor.map_map]
      simp [List.map_map, Function.comp_def, Prod.map]

include combineLaw zeroLaw coefficientLaw uniform in
theorem observe_equiv {J : Type} [DecidableEq J] (keys : J ≃ key.Value base)
    (sourceTerms : M → List (J × F))
    (termsEqual : ∀ message, generate message = (sourceTerms message).map (Prod.map keys id))
    {sumSlots : Nat} (sumBuffers : sum.program.code.memBound ≤ sumSlots) (sumReserve : sumSlots + 1 < 2 ^ w)
    (port : Interactive.Port w unifSpec) (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines port .unit layout.signing.rows.accumulation.cache.lookup.unit.representation
      layout.signing.rows.accumulation.cache.value.representation (fun _ => source) draw)
    (tape : RandomTape w) (value : layout.input.Value) (admitted : layout.ready value)
    (before : State w) (holds : layout.input.representation.Holds value before) :
    (fun result => (fun answer => (answer.val.1, answer.val.2.map (Prod.map keys.symm id))) <$>
        Interactive.observe (WeightedSignatureTail.output layout.signing).representation result) <$>
      (code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
        extract extractBuffers extractReserve sum sumBuffers sumReserve port draw).execute port .unit tape before =
      some <$> sourceProgram layout sourceTerms numerator calculate value
        (value.val.2.2.1.map (Prod.map keys.symm id)) (value.val.2.1.map (Prod.map keys.symm id)) := by
  have observed := (refines layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve sum sumBuffers sumReserve port drawCorrect).observe tape value admitted before holds
  have mapped := congrArg (fun computation : ProbComp (Option (WeightedSignatureTail.output layout.signing).Value) =>
    (fun result => (fun answer => (answer.val.1, answer.val.2.map (Prod.map keys.symm id))) <$> result) <$> computation) observed
  rw [← denote_equiv layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve sum combineLaw zeroLaw coefficientLaw source uniform keys sourceTerms termsEqual value admitted]
  simp only [Functor.map_map] at mapped ⊢
  exact mapped

end Signatures.Runtime.CaliperBackend.WeightedExtractor
