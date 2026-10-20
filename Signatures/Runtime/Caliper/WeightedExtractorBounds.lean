import Signatures.Runtime.Caliper.WeightedExtractor
import Signatures.Runtime.Caliper.WeightedExtractorTransitionBounds

/-! Bounds for complete extraction are derived from local routines and the
actual sampler, including all frame routing and saved context. -/
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

def hashTime (drawTime updateTime : Nat) : Nat :=
  TokenEvaluation.timeBudget layout.hashes drawTime updateTime +
    8 * layout.hashes.input.representation.encoding.words + 8 * layout.state.representation.encoding.words +
    12 * layout.context.representation.encoding.words
def hashWords (drawWords updateWords : Nat) : Nat :=
  TokenEvaluation.codeBudget layout.hashes drawWords updateWords +
    26 * layout.hashes.input.representation.encoding.words + 26 * layout.state.representation.encoding.words +
    39 * layout.context.representation.encoding.words + 42
def afterHashTime (generatorTime drawTime updateTime extractTime sumTime : Nat) : Nat :=
  transitionTime layout sumTime + WeightedSignatureTail.timeBudget layout.signing generatorTime drawTime updateTime extractTime
def afterHashWords (generatorWords drawWords updateWords extractWords sumWords : Nat) : Nat :=
  transitionWords layout sumWords + WeightedSignatureTail.codeBudget layout.signing generatorWords drawWords updateWords extractWords + 2
def timeBudget (generatorTime drawTime updateTime extractTime sumTime : Nat) : Nat :=
  8 * layout.hashInput.encoding.words +
    (hashTime layout drawTime updateTime + afterHashTime layout generatorTime drawTime updateTime extractTime sumTime)
def codeBudget (generatorWords drawWords updateWords extractWords sumWords : Nat) : Nat :=
  (26 * layout.hashInput.encoding.words + 14) +
    hashWords layout drawWords updateWords + afterHashWords layout generatorWords drawWords updateWords extractWords sumWords + 3
def badTimeBudget (generatorTime drawTime updateTime extractTime : Nat) : Nat :=
  8 * (WeightedSignatureTail.input layout.signing).encoding.words +
    WeightedSignatureTail.timeBudget layout.signing generatorTime drawTime updateTime extractTime
def badCodeBudget (generatorWords drawWords updateWords extractWords : Nat) : Nat :=
  (26 * (WeightedSignatureTail.input layout.signing).encoding.words + 14) +
    WeightedSignatureTail.codeBudget layout.signing generatorWords drawWords updateWords extractWords + 2

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.signing.rows.accumulation.cache.value.Value}
    {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.signing.rows.accumulation.cache.lookup.unit.representation
      layout.signing.rows.accumulation.cache.value.representation (fun _ => source) draw)
    {generatorTime generatorWords drawTime updateTime updateWords extractTime extractWords sumTime sumWords : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawBound : Interactive.TimeBound port .unit layout.signing.rows.accumulation.cache.lookup.unit.representation draw drawTime)
    (updateBound : update.BoundedBy updateTime updateWords) (extractBound : extract.BoundedBy extractTime extractWords)
    (sumBound : sum.BoundedBy sumTime sumWords)

include drawCorrect drawBound updateBound in
theorem hash_time : Interactive.TimeBoundOn layout.hashReady port .unit layout.hashInput
    (hashCode layout coefficientDefault zero default P comparison correct update updateBuffers reserve port draw)
    (hashTime layout drawTime updateTime) := by
  have refined := TokenEvaluation.refines layout.hashes coefficientDefault zero default P comparison correct
    update updateBuffers reserve port drawCorrect
  have bounded := TokenEvaluation.time_bound layout.hashes coefficientDefault zero default P comparison correct
    update updateBuffers reserve port drawCorrect drawBound updateBound
  have retained := (bounded.retain refined (by decide) layout.context.representation
    layout.signing.rows.accumulation.cache.wordFits layout.hashInput.fits).mono (Interactive.retain_time_unit_le _ _ _ _ _)
  exact fun tape value admitted before holds finished reached =>
    retained tape value (layout.hash_evaluation_ready value admitted) before holds finished reached

include drawCorrect generatorBound drawBound updateBound extractBound sumBound in
theorem afterHash_time : Interactive.TimeBoundOn layout.afterHashReady port .unit layout.hashOutput
    (afterHashCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve sum sumBuffers sumReserve port draw)
    (afterHashTime layout generatorTime drawTime updateTime extractTime sumTime) :=
  ((Interactive.TimeBound.compute (port := port) (cost := .unit) (transition layout sum sumBuffers sumReserve) _
    (transition_time layout sum sumBuffers sumReserve sumBound)).on layout.afterHashReady).seq
    ((Interactive.Refines.compute port .unit (transition layout sum sumBuffers sumReserve)).on layout.afterHashReady)
    (WeightedSignatureTail.time_bound layout.signing coefficientDefault zero default generator P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve port drawCorrect generatorBound drawBound updateBound extractBound)
    (by
      intro value admitted answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact transition_ready layout sum value admitted)
include drawCorrect generatorBound drawBound updateBound extractBound sumBound in
theorem time_bound : Interactive.TimeBoundOn layout.ready port .unit layout.input.representation
    (code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve sum sumBuffers sumReserve port draw)
    (timeBudget layout generatorTime drawTime updateTime extractTime sumTime) :=
  ((Interactive.TimeBound.compute (port := port) (cost := .unit) (prepare layout) _ (prepare_time layout)).on layout.ready).seq
    ((Interactive.Refines.compute port .unit (prepare layout)).on layout.ready)
    ((hash_time layout coefficientDefault zero default P comparison correct update updateBuffers reserve port drawCorrect drawBound updateBound).seq
      (hash_refines layout coefficientDefault zero default P comparison correct update updateBuffers reserve port drawCorrect)
      (afterHash_time layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
        extract extractBuffers extractReserve sum sumBuffers sumReserve port drawCorrect generatorBound drawBound updateBound extractBound sumBound)
      (hashPreserves layout coefficientDefault zero default P comparison correct update updateBuffers reserve)) (by
        intro value admitted answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact layout.prepare_ready value admitted)
include drawCorrect generatorBound drawBound updateBound extractBound in
theorem bad_time_bound : Interactive.TimeBoundOn layout.badReady port .unit layout.input.representation
    (badCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve port draw)
    (badTimeBudget layout generatorTime drawTime updateTime extractTime) :=
  ((Interactive.TimeBound.compute (port := port) (cost := .unit) (prepareBad layout) _ (prepareBad_time layout)).on layout.badReady).seq
    ((Interactive.Refines.compute port .unit (prepareBad layout)).on layout.badReady)
    (WeightedSignatureTail.time_bound layout.signing coefficientDefault zero default generator P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve port drawCorrect generatorBound drawBound updateBound extractBound) (by
        intro value admitted answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact admitted)

include updateBound in
theorem hash_words (draw : Interactive.Code w) {drawWords : Nat} (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords) :
    ((hashCode layout coefficientDefault zero default P comparison correct update updateBuffers reserve port draw).lower port).descriptionWords ≤
      hashWords layout drawWords updateWords := by
  have core := TokenEvaluation.code_bound layout.hashes coefficientDefault zero default P comparison correct
    update updateBuffers reserve port draw drawWordsBound updateBound
  have held := Interactive.retain_descriptionWords_le port
    (TokenEvaluation.code layout.hashes coefficientDefault zero default P comparison correct update updateBuffers reserve port draw)
    (Interactive.savedBuffer port (TokenEvaluation.code layout.hashes coefficientDefault zero default P comparison correct update updateBuffers reserve port draw))
    layout.hashes.input.representation.encoding.words layout.state.representation.encoding.words layout.context.representation.encoding.words
  change ((hashCode layout coefficientDefault zero default P comparison correct update updateBuffers reserve port draw).lower port).descriptionWords ≤ _ at held
  unfold hashWords
  omega
include generatorBound updateBound extractBound sumBound in
theorem afterHash_words (draw : Interactive.Code w) {drawWords : Nat} (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords) :
    ((afterHashCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve sum sumBuffers sumReserve port draw).lower port).descriptionWords ≤
      afterHashWords layout generatorWords drawWords updateWords extractWords sumWords := by
  have routed := transition_words layout sum sumBuffers sumReserve sumBound
  have tail := WeightedSignatureTail.code_bound layout.signing coefficientDefault zero default generator P comparison correct
    update updateBuffers reserve extract extractBuffers extractReserve port generatorBound updateBound extractBound draw drawWordsBound
  simp only [afterHashCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold afterHashWords
  omega
include generatorBound updateBound extractBound sumBound in
theorem code_bound (draw : Interactive.Code w) {drawWords : Nat} (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords) :
    ((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve sum sumBuffers sumReserve port draw).lower port).descriptionWords ≤
      codeBudget layout generatorWords drawWords updateWords extractWords sumWords := by
  have first := prepare_words layout
  have hashes := hash_words layout coefficientDefault zero default P comparison correct update updateBuffers reserve port updateBound draw drawWordsBound
  have tail := afterHash_words layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve sum sumBuffers sumReserve port generatorBound updateBound extractBound sumBound draw drawWordsBound
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega
include generatorBound updateBound extractBound in
theorem bad_code_bound (draw : Interactive.Code w) {drawWords : Nat} (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords) :
    ((badCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve port draw).lower port).descriptionWords ≤
      badCodeBudget layout generatorWords drawWords updateWords extractWords := by
  have first := prepareBad_words layout
  have tail := WeightedSignatureTail.code_bound layout.signing coefficientDefault zero default generator P comparison correct
    update updateBuffers reserve extract extractBuffers extractReserve port generatorBound updateBound extractBound draw drawWordsBound
  simp only [badCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold badCodeBudget
  omega

end Signatures.Runtime.CaliperBackend.WeightedExtractor
