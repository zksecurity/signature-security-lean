import Signatures.Runtime.Caliper.WeightedExtractionMemory

/-! The complete signing evaluator uses a bounded set of scratch buffers.
Its footprint is derived from the actual preparation and loop components,
so retaining another frame needs no assumed whole-extractor footprint. -/
namespace Signatures.Runtime.CaliperBackend.WeightedExtraction
open Caliper BoundedSource OracleComp OracleSpec
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
    (port : Interactive.Port w spec) (draw : Interactive.Code w)

theorem buffers {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots)
    (drawBound : (draw.lower port).memBound ≤ drawSlots) :
    ((code layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port draw).lower port).memBound ≤
      max 13 (max (generatorSlots + 3) (max (drawSlots + 5) (slots + 4))) := by
  have prepared := prepare_buffers layout coefficientDefault initial
  have body := WeightedToken.buffers layout.rows zero layout.terms layout.termCountFits layout.termStorageFits generator
    default P comparison correct update updateBuffers reserve port draw generatorBound drawBound
  have folded := InteractiveFold.buffers port
    (WeightedToken.code layout.rows zero layout.terms layout.termCountFits layout.termStorageFits generator
      default P comparison correct update updateBuffers reserve port draw)
    layout.rows.row.representation.encoding.words layout.rows.state.representation.encoding.words layout.capacity
  change ((WeightedTokenFold.code layout.rows zero layout.terms layout.termCountFits layout.termStorageFits generator
    default P comparison correct update updateBuffers reserve layout.capacity port draw).lower port).memBound ≤ _ at folded
  change max (prepare layout coefficientDefault initial).program.code.memBound
    ((WeightedTokenFold.code layout.rows zero layout.terms layout.termCountFits layout.termStorageFits generator
      default P comparison correct update updateBuffers reserve layout.capacity port draw).lower port).memBound ≤ _
  omega

theorem savedNameFits {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots) (generatorReserve : generatorSlots + 3 < 2 ^ w)
    (drawBound : WordIO.NamesBound (draw.lower port) drawSlots) (drawReserve : drawSlots + 5 < 2 ^ w)
    (updateReserve : slots + 4 < 2 ^ w) :
    Interactive.savedBuffer port
      (code layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port draw) < 2 ^ w := by
  have bound := buffers layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve
    port draw generatorBound drawBound.buffers
  have hw := layout.rows.accumulation.cache.wordFits
  unfold Interactive.savedBuffer
  omega

end Signatures.Runtime.CaliperBackend.WeightedExtraction
