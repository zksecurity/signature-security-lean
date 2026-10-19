import Signatures.Runtime.Caliper.CacheAccumulateBounds

/-! Stored descriptions, generated names and memory throughout the very same
interactive execution whose result and time are proved by the compiler. -/
namespace Signatures.Runtime.CaliperBackend.EncodedCacheAccumulate
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {F : Type}
    [DecidableEq (key.Value base)] (layout : CacheAccumulate.Layouts w (key.Value base) F (val.Value base))
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {I : Type} {spec : OracleSpec I}
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.combine layout.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    (port : Interactive.Port w spec) (draw : Interactive.Code w)

theorem buffers : ((code layout P comparison correct update updateBuffers reserve port draw).lower port).memBound ≤
    max (max 8 ((draw.lower port).memBound + 1) + 1) (max 4 slots + 1) := by
  have read := EncodedCacheRead.buffers layout.cache P comparison correct port draw
  have retained := Interactive.retain_buffers port (EncodedCacheRead.code layout.cache P comparison correct port draw)
    layout.cache.input.representation.encoding.words (CacheRead.output layout.cache).representation.encoding.words layout.saved.representation.encoding.words
  change ((retainedCode layout P comparison correct port draw).lower port).memBound ≤ _ at retained
  have finished := CacheAccumulate.finish_buffers layout update updateBuffers reserve
  change max ((retainedCode layout P comparison correct port draw).lower port).memBound
    (CacheAccumulate.finish layout update updateBuffers reserve).program.code.memBound ≤ _
  omega

theorem names {drawNames updateNames : Nat} (drawBound : WordIO.NamesBound (draw.lower port) drawNames)
    (updateBound : NamesAccounted update.program.code updateNames) :
    WordIO.NamesAccounted ((code layout P comparison correct update updateBuffers reserve port draw).lower port)
      (max (max 5 drawNames) updateNames) := by
  have read := (EncodedCacheRead.names layout.cache P comparison correct port draw drawBound).mono
    (Nat.le_max_left (max 5 drawNames) updateNames)
  have retained := Interactive.retain_names port read layout.cache.input.representation.encoding.words
    (CacheRead.output layout.cache).representation.encoding.words layout.saved.representation.encoding.words
  exact retained.seq (WordIO.NamesAccounted.compute (CacheAccumulate.finish_names layout _ update
    (updateBound.mono (Nat.le_max_right _ _)) updateBuffers reserve))

theorem descriptionFits (drawFits : (draw.lower port).DescriptionFits) {drawNames : Nat}
    (drawBound : WordIO.NamesBound (draw.lower port) drawNames) (namesFit : drawNames + 2 < 2 ^ w) :
    ((code layout P comparison correct update updateBuffers reserve port draw).lower port).DescriptionFits := by
  have readFits := EncodedCacheRead.descriptionFits layout.cache P comparison correct port draw drawFits drawBound (by omega)
  have savedFits : Interactive.savedBuffer port (EncodedCacheRead.code layout.cache P comparison correct port draw) < 2 ^ w := by
    have read := EncodedCacheRead.buffers layout.cache P comparison correct port draw
    have := drawBound.buffers
    have := layout.cache.wordFits
    dsimp only [Interactive.savedBuffer]
    omega
  have retained := Interactive.retain_descriptionFits port (EncodedCacheRead.code layout.cache P comparison correct port draw)
    (Interactive.savedBuffer port (EncodedCacheRead.code layout.cache P comparison correct port draw))
    layout.cache.input.representation.encoding.words (CacheRead.output layout.cache).representation.encoding.words layout.saved.representation.encoding.words
    layout.cache.wordFits readFits savedFits layout.cache.input.representation.fits layout.saved.representation.fits layout.returned.representation.fits
  exact WordIO.Code.DescriptionFits.seq layout.cache.wordFits retained
    (.compute (CacheAccumulate.finish layout update updateBuffers reserve).program.description_fits)

theorem staticMemory {drawWords updateTime updateWords drawNames updateNames : Nat}
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords) (updateBound : update.BoundedBy updateTime updateWords)
    (drawNamesBound : WordIO.NamesBound (draw.lower port) drawNames) (updateNamesBound : NamesAccounted update.program.code updateNames)
    (registers buffers : Nat) :
    ((code layout P comparison correct update updateBuffers reserve port draw).lower port).staticWords registers buffers ≤
      5 * codeBudget layout drawWords updateWords + 4 * max (max 5 drawNames) updateNames + registers + 3 * buffers := by
  have codeBound := code_bound layout P comparison correct update updateBuffers reserve port draw drawWordsBound updateBound
  rcases names layout P comparison correct update updateBuffers reserve port draw drawNamesBound updateNamesBound with ⟨registerBound, bufferBound⟩
  unfold WordIO.Code.staticWords
  omega

theorem memoryBound {drawSource : OracleComp spec layout.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
      (fun _ => drawSource) draw) {drawTime drawWords updateTime updateWords drawNames updateNames : Nat}
    (drawTimeBound : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords) (updateBound : update.BoundedBy updateTime updateWords)
    (drawNamesBound : WordIO.NamesBound (draw.lower port) drawNames) (updateNamesBound : NamesAccounted update.program.code updateNames)
    (tape : RandomTape w) (value : layout.input.Value) (before : State w)
    (holds : layout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout P comparison correct update updateBuffers reserve port draw).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout drawTime updateTime ∧
    ∃ execution : WordIO.Exec .unit tape ((code layout P comparison correct update updateBuffers reserve port draw).lower port)
        before finished.state finished.trace finished.time finished.net finished.peak,
      ∀ between, execution.Visits between →
        RegisterBound between (max registers ((code layout P comparison correct update updateBuffers reserve port draw).lower port).registerSlots) ∧
        between.SupportBound (max buffers ((code layout P comparison correct update updateBuffers reserve port draw).lower port).memBound) ∧ between.WellFormed ∧
        (((code layout P comparison correct update updateBuffers reserve port draw).lower port).staticWords registers buffers : Int) +
          between.liveMem (max buffers ((code layout P comparison correct update updateBuffers reserve port draw).lower port).memBound) ≤
            5 * codeBudget layout drawWords updateWords + 4 * max (max 5 drawNames) updateNames + registers + 3 * buffers +
              before.liveMem buffers + timeBudget layout drawTime updateTime := by
  have refined := refines layout P comparison correct update updateBuffers reserve port drawSource draw drawCorrect
  have bounded := time_bound layout P comparison correct update updateBuffers reserve port drawCorrect drawTimeBound updateBound
  have time := bounded tape value before holds finished reached
  have peak := bounded.bufferPeak refined (by decide) tape value before holds finished reached
  obtain ⟨answer, _, result, equal, _, _, execution⟩ := (refined tape value before holds).right_support reached
  cases Option.some.inj equal
  refine ⟨time, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ :=
    visited.total_memory_bound registers buffers initialRegisters initialBuffers holds.2.2.1
  refine ⟨registerBound, bufferBound, wellFormed, ?_⟩
  have staticBound := staticMemory layout P comparison correct update updateBuffers reserve port draw
    drawWordsBound updateBound drawNamesBound updateNamesBound registers buffers
  have initialMemory := liveMem_eq_of_supportBound initialBuffers
    (Nat.le_max_left buffers ((code layout P comparison correct update updateBuffers reserve port draw).lower port).memBound)
  omega

end Signatures.Runtime.CaliperBackend.EncodedCacheAccumulate
