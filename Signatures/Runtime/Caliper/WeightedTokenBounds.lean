import Signatures.Runtime.Caliper.WeightedToken

/-! Charged routing and generated evaluation, with buffer bounds derived from
primitive component footprints for retaining the body in an outer fold. -/
namespace Signatures.Runtime.CaliperBackend.WeightedToken
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M G F : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) M G F (val.Value base))
    (zero : layout.accumulation.cache.value.Value)
    (terms : Nat) (termCountFits : terms < 2 ^ w)
    (termStorageFits : 1 + terms * (WeightedRows.term layout.accumulation).representation.encoding.words +
      layout.state.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.weighted.message
      (GeneratedWeighted.terms layout.accumulation terms termCountFits termStorageFits) generate)
    (default : layout.accumulation.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.accumulation.combine layout.accumulation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I}

variable (port : Interactive.Port w spec) (draw : Interactive.Code w)

def timeBudget (generatorTime drawTime updateTime : Nat) :=
  8 * layout.weighted.input.representation.encoding.words +
    WeightedCoefficient.timeBudget layout.weighted terms termCountFits termStorageFits generatorTime drawTime updateTime
def codeBudget (generatorWords drawWords updateWords : Nat) :=
  26 * layout.weighted.input.representation.encoding.words + 16 +
    WeightedCoefficient.codeBudget layout.weighted terms termCountFits termStorageFits generatorWords drawWords updateWords

variable {source : OracleComp spec layout.accumulation.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.accumulation.cache.lookup.unit.representation
      layout.accumulation.cache.value.representation (fun _ => source) draw)
include drawCorrect in
theorem time_bound {generatorTime generatorWords drawTime updateTime updateWords : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawBound : Interactive.TimeBound port .unit layout.accumulation.cache.lookup.unit.representation draw drawTime)
    (updateBound : update.BoundedBy updateTime updateWords) :
    Interactive.TimeBoundOn (ready layout (generate := generate)) port .unit layout.input
      (code layout zero terms termCountFits termStorageFits generator default P comparison correct update updateBuffers reserve port draw)
      (timeBudget layout terms termCountFits termStorageFits generatorTime drawTime updateTime) :=
  ((Interactive.TimeBound.compute (port := port) (cost := .unit) (prepare layout) _
    (ByteRoute.time _ _ _ (parts layout) layout.accumulation.cache.wordFits
      (parts_valid layout) (parts_words layout) (argument_bytes layout))).on (ready layout (generate := generate))).seq
    ((Interactive.Refines.compute port .unit (prepare layout)).on (ready layout (generate := generate)))
    (WeightedCoefficient.time_bound layout.weighted zero terms termCountFits termStorageFits generator default
      P comparison correct update updateBuffers reserve port draw drawCorrect generatorBound drawBound updateBound) (by
        intro value admitted answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact admitted)

theorem code_bound {generatorTime generatorWords drawWords updateTime updateWords : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawBound : (draw.lower port).descriptionWords ≤ drawWords)
    (updateBound : update.BoundedBy updateTime updateWords) :
    ((code layout zero terms termCountFits termStorageFits generator default P comparison correct
      update updateBuffers reserve port draw).lower port).descriptionWords ≤
      codeBudget layout terms termCountFits termStorageFits generatorWords drawWords updateWords := by
  have prepared := ByteRoute.codeWords _ _ _ (parts layout) layout.accumulation.cache.wordFits
    (parts_valid layout) (parts_words layout) (argument_bytes layout)
  have core := WeightedCoefficient.code_bound layout.weighted zero terms termCountFits termStorageFits generator default
    P comparison correct update updateBuffers reserve port draw generatorBound drawBound updateBound
  change descriptionWords (prepare layout).code ≤ _ at prepared
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names {generatorNames drawNames updateNames : Nat}
    (generatorBound : NamesAccounted generator.program.code generatorNames)
    (drawBound : WordIO.NamesBound (draw.lower port) drawNames)
    (updateBound : NamesAccounted update.program.code updateNames) :
    WordIO.NamesAccounted ((code layout zero terms termCountFits termStorageFits generator default P comparison correct
      update updateBuffers reserve port draw).lower port)
      (max generatorNames (max (max 5 drawNames) updateNames)) :=
  (WordIO.NamesAccounted.compute (ByteRoute.names _ _ _ (parts layout) layout.accumulation.cache.wordFits
    (parts_valid layout) (parts_words layout) (argument_bytes layout) _)).seq
    (WeightedCoefficient.names layout.weighted zero terms termCountFits termStorageFits generator default
      P comparison correct update updateBuffers reserve port draw generatorBound drawBound updateBound)

theorem buffers {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots)
    (drawBound : (draw.lower port).memBound ≤ drawSlots) :
    ((code layout zero terms termCountFits termStorageFits generator default P comparison correct
      update updateBuffers reserve port draw).lower port).memBound ≤
      max 12 (max (generatorSlots + 2) (max (drawSlots + 4) (slots + 3))) := by
  have core := GeneratedWeighted.buffers layout.accumulation layout.weighted.message terms termCountFits termStorageFits
    generator port default P comparison correct update updateBuffers reserve draw
  have retained := Interactive.retain_buffers port
    (WeightedCoefficient.evaluator layout.weighted terms termCountFits termStorageFits generator default
      P comparison correct update updateBuffers reserve port draw)
    layout.weighted.evaluationInput.encoding.words layout.state.representation.encoding.words
    layout.accumulation.saved.representation.encoding.words
  have started := ByteRoute.buffers _ _ _ (WeightedCoefficient.prepareParts layout.weighted zero)
    layout.accumulation.cache.wordFits (WeightedCoefficient.prepareParts_valid layout.weighted zero)
    (WeightedCoefficient.prepareParts_words layout.weighted zero) (WeightedCoefficient.prepare_bytes layout.weighted zero)
  have routed := ByteRoute.buffers _ _ _ (parts layout) layout.accumulation.cache.wordFits
    (parts_valid layout) (parts_words layout) (argument_bytes layout)
  have ended := CacheAccumulate.finish_buffers layout.accumulation update updateBuffers reserve
  change ((WeightedCoefficient.evaluator layout.weighted terms termCountFits termStorageFits generator default
    P comparison correct update updateBuffers reserve port draw).lower port).memBound ≤ _ at core
  change ((WeightedCoefficient.evaluate layout.weighted terms termCountFits termStorageFits generator default
    P comparison correct update updateBuffers reserve port draw).lower port).memBound ≤ _ at retained
  change (WeightedCoefficient.prepare layout.weighted zero).code.memBound ≤ 2 at started
  change (prepare layout).code.memBound ≤ 2 at routed
  change (WeightedCoefficient.tail layout.weighted update updateBuffers reserve).code.memBound ≤ _ at ended
  change max (prepare layout).code.memBound
    (max (WeightedCoefficient.prepare layout.weighted zero).code.memBound
      (max ((WeightedCoefficient.evaluate layout.weighted terms termCountFits termStorageFits generator default
        P comparison correct update updateBuffers reserve port draw).lower port).memBound
        (WeightedCoefficient.tail layout.weighted update updateBuffers reserve).code.memBound)) ≤ _
  omega

theorem descriptionFits {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots) (generatorReserve : generatorSlots + 1 < 2 ^ w)
    (drawFits : (draw.lower port).DescriptionFits)
    (drawBound : WordIO.NamesBound (draw.lower port) drawSlots) (drawReserve : drawSlots + 3 < 2 ^ w) :
    ((code layout zero terms termCountFits termStorageFits generator default P comparison correct
      update updateBuffers reserve port draw).lower port).DescriptionFits :=
  .seq layout.accumulation.cache.wordFits (.compute (prepare layout).description_fits)
    (WeightedCoefficient.descriptionFits layout.weighted zero terms termCountFits termStorageFits generator default
      P comparison correct update updateBuffers reserve port draw generatorBound generatorReserve drawFits drawBound drawReserve)

end Signatures.Runtime.CaliperBackend.WeightedToken
