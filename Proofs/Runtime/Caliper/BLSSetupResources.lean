import Proofs.Runtime.Caliper.BLSSetupSampling

/-! Complete sampled-setup resources, including retained input, generated names,
stored sampler/scale code and every intermediate memory state. -/

namespace Signatures.Runtime.CaliperBackend.BLSSetup
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {M F G K : Type} (layout : Layouts w M F G K)
    (port : Interactive.Port w unifSpec)

theorem good_time : Interactive.TimeBound port .unit layout.challenge.representation (goodCode layout) (200 * layout.width) :=
  Interactive.TimeBound.compute (port := port) (cost := .unit) (good layout).program _ (good_bounded layout).time_le

theorem good_words : ((goodCode layout).lower port).descriptionWords ≤ 700 * layout.width + 251 := by
  have bounded := (good_bounded layout).code_le
  simp only [goodCode, Interactive.Code.lower, WordIO.Code.descriptionWords_compute]
  omega

variable (draw : Interactive.Code w) (drawSource : ProbComp layout.scheme.cache.value.Value)
    (drawCorrect : Interactive.Refines port .unit layout.scheme.cache.lookup.unit.representation
      layout.scheme.cache.value.representation (fun _ => drawSource) draw)
    {drawTime drawWords : Nat}
    (drawTimeBound : Interactive.TimeBound port .unit layout.scheme.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords)

include drawCorrect drawTimeBound in
theorem sample_time : Interactive.TimeBound port .unit layout.challenge.representation (sample layout port draw)
    (drawTime + 8 * layout.scheme.cache.value.representation.encoding.words + 12 * layout.challenge.representation.encoding.words) := by
  have saved := drawTimeBound.retain drawCorrect (by decide) layout.challenge.representation layout.scheme.cache.wordFits
    (by change 0 + layout.challenge.representation.encoding.words < 2 ^ w; simpa only [Nat.zero_add] using layout.challenge.representation.fits)
  have viewed := saved.viewInput layout.challenge.representation (fun value => (⟨(), trivial⟩, value)) (fun _ => rfl)
  exact viewed.mono (Interactive.retain_time_unit_le _ 0 _ _ _)

variable [SMul F K]
    (scale : Implementation .unit layout.scaleArgs layout.key (fun value => value.1 • value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)
    {scaleTime scaleWords : Nat} (scaleBound : scale.BoundedBy scaleTime scaleWords)

def badTime (drawTime scaleTime : Nat) : Nat := drawTime + scaleTime + 720 * layout.width
def badWords (drawWords scaleWords : Nat) : Nat := drawWords + scaleWords + 2300 * layout.width + 700

include drawCorrect drawTimeBound scaleBound in
theorem bad_time : Interactive.TimeBound port .unit layout.challenge.representation
    (badCode layout port draw scale scaleBuffers reserve) (badTime layout drawTime scaleTime) := by
  have localBound := Interactive.TimeBound.compute (port := port) (cost := .unit) (badLocal layout scale scaleBuffers reserve).program _
    (badLocal_bounded layout scale scaleBuffers reserve scaleBound).time_le
  apply ((sample_time layout port draw drawSource drawCorrect drawTimeBound).seq
    (sample_refines layout port draw drawSource drawCorrect) localBound).mono
  have := layout.sizes
  dsimp only [badTime]
  omega

include drawWordsBound scaleBound in
theorem bad_words : ((badCode layout port draw scale scaleBuffers reserve).lower port).descriptionWords ≤ badWords layout drawWords scaleWords := by
  have sampled := Interactive.retain_descriptionWords_le port draw (Interactive.savedBuffer port draw) 0
    layout.scheme.cache.value.representation.encoding.words layout.challenge.representation.encoding.words
  have localBound := (badLocal_bounded layout scale scaleBuffers reserve scaleBound).code_le
  have := layout.sizes
  change ((sample layout port draw).lower port).descriptionWords ≤ _ at sampled
  simp only [badCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  dsimp only [badWords]
  omega

theorem bad_names {drawSlots scaleSlots : Nat}
    (drawNames : WordIO.NamesBound (draw.lower port) drawSlots)
    (scaleNames : NamesAccounted scale.program.code scaleSlots) :
    WordIO.NamesAccounted ((badCode layout port draw scale scaleBuffers reserve).lower port) (max (max 3 drawSlots) scaleSlots) := by
  have sampled := Interactive.retain_names port drawNames.accounted 0
    layout.scheme.cache.value.representation.encoding.words layout.challenge.representation.encoding.words
  have localNames := WordIO.NamesAccounted.compute (badLocal_names layout scaleSlots scale scaleNames scaleBuffers reserve)
  exact (sampled.mono (by omega)).seq (localNames.mono (by omega))

theorem bad_descriptionFits {drawSlots : Nat}
    (drawFits : (draw.lower port).DescriptionFits)
    (drawNames : WordIO.NamesBound (draw.lower port) drawSlots) (drawReserve : drawSlots < 2 ^ w) :
    ((badCode layout port draw scale scaleBuffers reserve).lower port).DescriptionFits := by
  have named : Interactive.savedBuffer port draw < 2 ^ w := by
    have bound := drawNames.buffers
    have width := layout.scheme.cache.wordFits
    dsimp only [Interactive.savedBuffer]
    omega
  have sampled := Interactive.retain_descriptionFits port draw (Interactive.savedBuffer port draw) 0
    layout.scheme.cache.value.representation.encoding.words layout.challenge.representation.encoding.words layout.scheme.cache.wordFits
    drawFits named (by positivity) layout.challenge.representation.fits layout.sampled.representation.fits
  exact sampled.seq layout.scheme.cache.wordFits (.compute (badLocal layout scale scaleBuffers reserve).program.description_fits)

include drawCorrect drawTimeBound drawWordsBound scaleBound in
theorem bad_resources {drawSlots scaleSlots : Nat}
    (drawNames : WordIO.NamesBound (draw.lower port) drawSlots)
    (scaleNames : NamesAccounted scale.program.code scaleSlots)
    (tape : RandomTape w) (value : layout.challenge.Value) (before : State w)
    (holds : layout.challenge.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((badCode layout port draw scale scaleBuffers reserve).execute port .unit tape before)) :
    let code := badCode layout port draw scale scaleBuffers reserve
    let words := badWords layout drawWords scaleWords
    let time := badTime layout drawTime scaleTime
    let names := max (max 3 drawSlots) scaleSlots
    finished.time ≤ time ∧ ∃ answer ∈ support (badSource layout drawSource scale scaleBuffers reserve value),
      layout.badOutput.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (code.lower port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers (code.lower port).registerSlots) ∧
          between.SupportBound (max buffers (code.lower port).memBound) ∧ between.WellFormed ∧
          ((code.lower port).staticWords registers buffers : Int) + between.liveMem (max buffers (code.lower port).memBound) ≤
            words + 4 * (names + words) + registers + 3 * buffers + before.liveMem buffers + time := by
  have refined := bad_refines layout port draw drawSource drawCorrect scale scaleBuffers reserve
  have bounded := bad_time layout port draw drawSource drawCorrect drawTimeBound scale scaleBuffers reserve scaleBound
  have stored := bad_words layout port draw drawWordsBound scale scaleBuffers reserve scaleBound
  have named := bad_names layout port draw scale scaleBuffers reserve drawNames scaleNames
  exact refined.resources bounded stored
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
    tape value before holds registers buffers initialRegisters initialBuffers finished reached

end Signatures.Runtime.CaliperBackend.BLSSetup
