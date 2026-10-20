import Signatures.Runtime.Caliper.WeightedExtractorTransition

/-! Complete weighted extraction executes hash evaluation, local numerator
arithmetic, signing evaluation and target extraction with one private cache.
The pair-valued bad branch executes the same tail after its paid input route. -/
namespace Signatures.Runtime.CaliperBackend.WeightedExtractor
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M G F : Type}
    [DecidableEq (key.Value base)] (layout : Layouts w (key.Value base) M G F (val.Value base))
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
    {sumSlots : Nat} (sumBuffers : sum.program.code.memBound ≤ sumSlots) (sumReserve : sumSlots + 1 < 2 ^ w)
    {I : Type} {spec : OracleSpec I}


def hashCode (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  let body := TokenEvaluation.code layout.hashes coefficientDefault zero default
    P comparison correct update updateBuffers reserve port draw
  Interactive.retain body (Interactive.savedBuffer port body)
    layout.hashes.input.representation.encoding.words layout.state.representation.encoding.words
    layout.context.representation.encoding.words
def hashDenote (source : OracleComp spec layout.signing.rows.accumulation.cache.value.Value) (value : layout.HashInput) :
    OracleComp spec layout.HashOutput :=
  (fun answer => (answer, value.2)) <$>
    TokenEvaluation.denote layout.hashes coefficientDefault zero default P comparison correct update updateBuffers reserve source value.1
def afterHashCode (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (transition layout sum sumBuffers sumReserve).code)
    (WeightedSignatureTail.code layout.signing coefficientDefault zero default generator P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve port draw)
def afterHashDenote (source : OracleComp spec layout.signing.rows.accumulation.cache.value.Value) (value : layout.HashOutput) :
    OracleComp spec (WeightedSignatureTail.output layout.signing).Value :=
  WeightedSignatureTail.denote layout.signing coefficientDefault zero default generator P comparison correct
    update updateBuffers reserve extract extractBuffers extractReserve source (transitionValue layout sum value)
def code (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (prepare layout).code)
    (.seq (hashCode layout coefficientDefault zero default P comparison correct update updateBuffers reserve port draw)
      (afterHashCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
        extract extractBuffers extractReserve sum sumBuffers sumReserve port draw))
def denote (source : OracleComp spec layout.signing.rows.accumulation.cache.value.Value) (value : layout.input.Value) :
    OracleComp spec (WeightedSignatureTail.output layout.signing).Value :=
  hashDenote layout coefficientDefault zero default P comparison correct update updateBuffers reserve source (layout.preparedValue value) >>=
    afterHashDenote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve sum source
def badCode (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (prepareBad layout).code)
    (WeightedSignatureTail.code layout.signing coefficientDefault zero default generator P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve port draw)
def badDenote (source : OracleComp spec layout.signing.rows.accumulation.cache.value.Value) (value : layout.input.Value) :
    OracleComp spec (WeightedSignatureTail.output layout.signing).Value :=
  WeightedSignatureTail.denote layout.signing coefficientDefault zero default generator P comparison correct
    update updateBuffers reserve extract extractBuffers extractReserve source (layout.signatureValue value)

theorem hashPreserves {source : OracleComp spec layout.signing.rows.accumulation.cache.value.Value}
    (value : layout.HashInput) (admitted : layout.hashReady value) (answer : layout.HashOutput)
    (reached : answer ∈ support (hashDenote layout coefficientDefault zero default P comparison correct
      update updateBuffers reserve source value)) : layout.afterHashReady answer := by
  obtain ⟨result, supported, rfl⟩ := mem_support_map_peel
    (fun result => (result, value.2))
    (TokenEvaluation.denote layout.hashes coefficientDefault zero default P comparison correct update updateBuffers reserve source value.1) reached
  have room := TokenEvaluation.remaining_room layout.hashes coefficientDefault zero default P comparison correct
    update updateBuffers reserve source value.1
    (layout.signing.terms * value.2.val.2.1.length + layout.signing.terms)
    (by simpa only [Layouts.hashReady, Layouts.hashes, hashRows, Nat.add_assoc] using admitted) result supported
  simpa only [Layouts.afterHashReady, RowEvaluation.room, Layouts.hashes, hashRows, Nat.add_assoc] using room

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.signing.rows.accumulation.cache.value.Value}
    {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.signing.rows.accumulation.cache.lookup.unit.representation
      layout.signing.rows.accumulation.cache.value.representation (fun _ => source) draw)
include drawCorrect in
theorem hash_refines : Interactive.RefinesOn layout.hashReady port .unit layout.hashInput layout.hashOutput
    (hashDenote layout coefficientDefault zero default P comparison correct update updateBuffers reserve source)
    (hashCode layout coefficientDefault zero default P comparison correct update updateBuffers reserve port draw) := by
  have retained := (TokenEvaluation.refines layout.hashes coefficientDefault zero default P comparison correct
    update updateBuffers reserve port drawCorrect).retain (by decide) layout.context.representation
    layout.signing.rows.accumulation.cache.wordFits layout.hashInput.fits layout.hashOutput.fits
  exact fun tape value admitted before holds =>
    retained tape value (layout.hash_evaluation_ready value admitted) before holds
include drawCorrect in
theorem afterHash_refines : Interactive.RefinesOn layout.afterHashReady port .unit layout.hashOutput
    (WeightedSignatureTail.output layout.signing).representation
    (afterHashDenote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve sum source)
    (afterHashCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve sum sumBuffers sumReserve port draw) := by
  have composed := ((Interactive.Refines.compute port .unit (transition layout sum sumBuffers sumReserve)).on layout.afterHashReady).seq
    (WeightedSignatureTail.refines layout.signing coefficientDefault zero default generator P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve port drawCorrect) (by
        intro value admitted answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact transition_ready layout sum value admitted)
  convert composed using 1
  · funext value
    exact (pure_bind _ _).symm
  · rfl
include drawCorrect in
theorem refines : Interactive.RefinesOn layout.ready port .unit layout.input.representation
    (WeightedSignatureTail.output layout.signing).representation
    (denote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve sum source)
    (code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve sum sumBuffers sumReserve port draw) := by
  have body := (hash_refines layout coefficientDefault zero default P comparison correct update updateBuffers reserve port drawCorrect).seq
    (afterHash_refines layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve sum sumBuffers sumReserve port drawCorrect)
    (hashPreserves layout coefficientDefault zero default P comparison correct update updateBuffers reserve)
  have composed := ((Interactive.Refines.compute port .unit (prepare layout)).on layout.ready).seq body (by
    intro value admitted answer reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst answer
    exact layout.prepare_ready value admitted)
  convert composed using 1
  · funext value
    exact (pure_bind _ _).symm
  · rfl
include drawCorrect in
theorem bad_refines : Interactive.RefinesOn layout.badReady port .unit layout.input.representation
    (WeightedSignatureTail.output layout.signing).representation
    (badDenote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve source)
    (badCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve port draw) := by
  have composed := ((Interactive.Refines.compute port .unit (prepareBad layout)).on layout.badReady).seq
    (WeightedSignatureTail.refines layout.signing coefficientDefault zero default generator P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve port drawCorrect) (by
        intro value admitted answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact admitted)
  convert composed using 1
  · funext value
    exact (pure_bind _ _).symm
  · rfl

end Signatures.Runtime.CaliperBackend.WeightedExtractor
