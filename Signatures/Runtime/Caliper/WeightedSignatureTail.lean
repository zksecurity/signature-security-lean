import Signatures.Runtime.Caliper.WeightedSignatureTailLayout

/-! The complete signing/target tail is one executed program. Its private
cache passes directly between the two evaluations, with room for the target
proved from the signing evaluator's supported-result postcondition. -/
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

def evaluationCode (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  let body := WeightedExtraction.code layout coefficientDefault zero zero default generator
    P comparison correct update updateBuffers reserve port draw
  Interactive.retain body (Interactive.savedBuffer port body)
    layout.input.representation.encoding.words layout.rows.state.representation.encoding.words
    (context layout).representation.encoding.words
def evaluation (source : OracleComp spec layout.rows.accumulation.cache.value.Value) (value : Input layout) :
    OracleComp spec (Returned layout) :=
  (fun answer => (answer, value.2)) <$>
    WeightedExtraction.denote layout coefficientDefault zero zero default generator
      P comparison correct update updateBuffers reserve source value.1
def finalReady (value : Returned layout) : Prop :=
  WeightedCoefficient.valid layout.rows.weighted (generate := generate) (argument layout value)
def finishCode (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (route layout).code)
    (WeightedTarget.code layout.rows.weighted zero layout.terms layout.termCountFits layout.termStorageFits
      generator default P comparison correct update updateBuffers reserve extract extractBuffers extractReserve port draw)
def finish (source : OracleComp spec layout.rows.accumulation.cache.value.Value) (value : Returned layout) :
    OracleComp spec (output layout).Value :=
  WeightedTarget.denote layout.rows.weighted zero layout.terms layout.termCountFits layout.termStorageFits
    generator default P comparison correct update updateBuffers reserve extract extractBuffers extractReserve source
      (argument layout value)
def code (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (evaluationCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve port draw)
    (finishCode layout zero default generator P comparison correct update updateBuffers reserve extract extractBuffers extractReserve port draw)
def denote (source : OracleComp spec layout.rows.accumulation.cache.value.Value) (value : Input layout) :
    OracleComp spec (output layout).Value :=
  evaluation layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve source value >>=
    finish layout zero default generator P comparison correct update updateBuffers reserve extract extractBuffers extractReserve source

theorem preserves {source : OracleComp spec layout.rows.accumulation.cache.value.Value}
    (value : Input layout) (admitted : ready layout value) (answer : Returned layout)
    (reached : answer ∈ support
      (evaluation layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve source value)) :
    finalReady layout (generate := generate) answer := by
  simp only [evaluation, support_map, Set.mem_image] at reached
  obtain ⟨result, supported, rfl⟩ := reached
  have room := WeightedExtraction.remaining_room layout coefficientDefault zero zero default generator
    P comparison correct update updateBuffers reserve source value.1 layout.terms admitted result supported
  have generated := (generator.preserves value.2.val.1 value.2.property.1).1
  change (generate value.2.val.1).length ≤ layout.terms at generated
  change result.val.2.length + (generate value.2.val.1).length ≤ layout.rows.accumulation.cache.capacityPred + 1
  omega

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.rows.accumulation.cache.value.Value}
    {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) draw)
include drawCorrect in
theorem evaluation_refines :
    Interactive.RefinesOn (ready layout) port .unit (input layout) (returned layout)
      (evaluation layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve source)
      (evaluationCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve port draw) := by
  have retained := (WeightedExtraction.refines layout coefficientDefault zero zero default generator
    P comparison correct update updateBuffers reserve port drawCorrect).retain (by decide)
    (context layout).representation layout.rows.accumulation.cache.wordFits (input layout).fits (returned layout).fits
  exact fun tape value admitted before holds =>
    retained tape value (signing_ready layout value admitted) before holds
include drawCorrect in
theorem finish_refines :
    Interactive.RefinesOn (finalReady layout (generate := generate)) port .unit (returned layout) (output layout).representation
      (finish layout zero default generator P comparison correct update updateBuffers reserve extract extractBuffers extractReserve source)
      (finishCode layout zero default generator P comparison correct update updateBuffers reserve extract extractBuffers extractReserve port draw) := by
  have composed := ((Interactive.Refines.compute port .unit (route layout)).on
    (finalReady layout (generate := generate))).seq
    (WeightedTarget.refines layout.rows.weighted zero layout.terms layout.termCountFits layout.termStorageFits
      generator default P comparison correct update updateBuffers reserve extract extractBuffers extractReserve port draw drawCorrect) (by
        intro value admitted answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact admitted)
  convert composed using 1
  · funext value
    exact (pure_bind _ _).symm
  · rfl
include drawCorrect in
theorem refines : Interactive.RefinesOn (ready layout) port .unit (input layout) (output layout).representation
    (denote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve source)
    (code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve port draw) :=
  (evaluation_refines layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve port drawCorrect).seq
    (finish_refines layout zero default generator P comparison correct update updateBuffers reserve extract extractBuffers extractReserve port drawCorrect)
    (preserves layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve)

end Signatures.Runtime.CaliperBackend.WeightedSignatureTail
