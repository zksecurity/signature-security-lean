import Proofs.Runtime.Caliper.WeightedSignatureTail
import Proofs.Runtime.Caliper.WeightedExtractionBuffers

/-! Derived runtime and stored-code budgets for the composed signing/target
program, including retention and the executed input permutation. -/
namespace Signatures.Runtime.CaliperBackend.WeightedSignatureTail
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M G F : Type}
    [DecidableEq (key.Value base)] (layout : WeightedExtraction.Layouts w (key.Value base) M G F (val.Value base))
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
    {I : Type} {spec : OracleSpec I}

def evaluationTime (generatorTime drawTime updateTime : Nat) : Nat :=
  WeightedExtraction.timeBudget layout generatorTime drawTime updateTime +
    8 * layout.input.representation.encoding.words + 8 * layout.rows.state.representation.encoding.words +
    12 * (context layout).representation.encoding.words
def finishTime (generatorTime drawTime updateTime extractTime : Nat) : Nat :=
  8 * (returned layout).encoding.words +
    WeightedTarget.timeBudget layout.rows.weighted layout.terms layout.termCountFits layout.termStorageFits
      generatorTime drawTime updateTime extractTime
def timeBudget (generatorTime drawTime updateTime extractTime : Nat) : Nat :=
  evaluationTime layout generatorTime drawTime updateTime + finishTime layout generatorTime drawTime updateTime extractTime
def evaluationWords (generatorWords drawWords updateWords : Nat) : Nat :=
  WeightedExtraction.codeBudget layout generatorWords drawWords updateWords +
    26 * layout.input.representation.encoding.words + 26 * layout.rows.state.representation.encoding.words +
    39 * (context layout).representation.encoding.words + 42
def finishWords (generatorWords drawWords updateWords extractWords : Nat) : Nat :=
  (26 * (returned layout).encoding.words + 14) +
    WeightedTarget.codeBudget layout.rows.weighted layout.terms layout.termCountFits layout.termStorageFits
      generatorWords drawWords updateWords extractWords + 2
def codeBudget (generatorWords drawWords updateWords extractWords : Nat) : Nat :=
  evaluationWords layout generatorWords drawWords updateWords +
    finishWords layout generatorWords drawWords updateWords extractWords + 1

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.rows.accumulation.cache.value.Value}
    {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) draw)
    {generatorTime generatorWords drawTime updateTime updateWords extractTime extractWords : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawBound : Interactive.TimeBound port .unit layout.rows.accumulation.cache.lookup.unit.representation draw drawTime)
    (updateBound : update.BoundedBy updateTime updateWords)
    (extractBound : extract.BoundedBy extractTime extractWords)

include drawCorrect generatorBound drawBound updateBound in
theorem evaluation_time :
    Interactive.TimeBoundOn (ready layout) port .unit (input layout)
      (evaluationCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve port draw)
      (evaluationTime layout generatorTime drawTime updateTime) := by
  have refined := WeightedExtraction.refines layout coefficientDefault zero zero default generator
    P comparison correct update updateBuffers reserve port drawCorrect
  have bounded := WeightedExtraction.time_bound layout coefficientDefault zero zero default generator
    P comparison correct update updateBuffers reserve port drawCorrect generatorBound drawBound updateBound
  have retained := (bounded.retain refined (by decide) (context layout).representation
    layout.rows.accumulation.cache.wordFits (input layout).fits).mono (Interactive.retain_time_unit_le _ _ _ _ _)
  exact fun tape value admitted before holds finished reached =>
    retained tape value (signing_ready layout value admitted) before holds finished reached

include drawCorrect generatorBound drawBound updateBound extractBound in
theorem finish_time :
    Interactive.TimeBoundOn (finalReady layout (generate := generate)) port .unit (returned layout)
      (finishCode layout zero default generator P comparison correct update updateBuffers reserve extract extractBuffers extractReserve port draw)
      (finishTime layout generatorTime drawTime updateTime extractTime) :=
  ((Interactive.TimeBound.compute (port := port) (cost := .unit) (route layout) _ (route_time layout)).on
    (finalReady layout (generate := generate))).seq
    ((Interactive.Refines.compute port .unit (route layout)).on (finalReady layout (generate := generate)))
    (WeightedTarget.time_bound layout.rows.weighted zero layout.terms layout.termCountFits layout.termStorageFits
      generator default P comparison correct update updateBuffers reserve extract extractBuffers extractReserve
      port draw drawCorrect generatorBound drawBound updateBound extractBound) (by
        intro value admitted answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact admitted)

include drawCorrect generatorBound drawBound updateBound extractBound in
theorem time_bound :
    Interactive.TimeBoundOn (ready layout) port .unit (input layout)
      (code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
        extract extractBuffers extractReserve port draw)
      (timeBudget layout generatorTime drawTime updateTime extractTime) :=
  (evaluation_time layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    port drawCorrect generatorBound drawBound updateBound).seq
    (evaluation_refines layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve port drawCorrect)
    (finish_time layout zero default generator P comparison correct update updateBuffers reserve extract extractBuffers extractReserve
      port drawCorrect generatorBound drawBound updateBound extractBound)
    (preserves layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve)

include generatorBound updateBound in
theorem evaluation_words (draw : Interactive.Code w) {drawWords : Nat}
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords) :
    ((evaluationCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve port draw).lower port).descriptionWords ≤
      evaluationWords layout generatorWords drawWords updateWords := by
  have core := WeightedExtraction.code_bound layout coefficientDefault zero zero default generator
    P comparison correct update updateBuffers reserve port draw generatorBound drawWordsBound updateBound
  have retained := Interactive.retain_descriptionWords_le port
    (WeightedExtraction.code layout coefficientDefault zero zero default generator P comparison correct update updateBuffers reserve port draw)
    (Interactive.savedBuffer port
      (WeightedExtraction.code layout coefficientDefault zero zero default generator P comparison correct update updateBuffers reserve port draw))
    layout.input.representation.encoding.words layout.rows.state.representation.encoding.words
    (context layout).representation.encoding.words
  change ((evaluationCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve port draw).lower port).descriptionWords ≤ _ at retained
  unfold evaluationWords
  omega

include generatorBound updateBound extractBound in
theorem finish_words (draw : Interactive.Code w) {drawWords : Nat}
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords) :
    ((finishCode layout zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve port draw).lower port).descriptionWords ≤
      finishWords layout generatorWords drawWords updateWords extractWords := by
  have routed := route_words layout
  have target := WeightedTarget.code_bound layout.rows.weighted zero layout.terms layout.termCountFits layout.termStorageFits
    generator default P comparison correct update updateBuffers reserve extract extractBuffers extractReserve
    port draw generatorBound drawWordsBound updateBound extractBound
  simp only [finishCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold finishWords
  omega

include generatorBound updateBound extractBound in
theorem code_bound (draw : Interactive.Code w) {drawWords : Nat}
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords) :
    ((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve port draw).lower port).descriptionWords ≤
      codeBudget layout generatorWords drawWords updateWords extractWords := by
  have first := evaluation_words layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    port generatorBound updateBound draw drawWordsBound
  have second := finish_words layout zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve port generatorBound updateBound extractBound draw drawWordsBound
  simpa only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, codeBudget]
    using Nat.add_le_add_right (Nat.add_le_add first second) 1

end Signatures.Runtime.CaliperBackend.WeightedSignatureTail
