import Signatures.Runtime.Caliper.WeightedBadSetup

/-! Bounds for the executed scalar draw, retained challenge and computed key.
Only the individual sampler and key-scaling routine supply primitive budgets. -/
namespace Signatures.Runtime.CaliperBackend.WeightedBadSetup
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F G PK : Type} (layout : Layouts w F G PK)

theorem scalar_bounded : (scalar layout).BoundedBy (8 * layout.scalar.representation.encoding.words)
    (26 * layout.scalar.representation.encoding.words + 14) := Implementation.first_boundedBy _ _ _ _
theorem points_bounded : (points layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals have := layout.sizes; dsimp only [Layouts.challenge, Layouts.keys] at this ⊢; omega
theorem generator_bounded : (generator layout).BoundedBy (24 * layout.width) (78 * layout.width + 44) := by
  apply (((Implementation.second_boundedBy _ _ _ _).then (Implementation.second_boundedBy _ _ _ _)).then
    (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals have := layout.sizes; dsimp only [Layouts.challenge, Layouts.keys] at this ⊢; omega
theorem config_bounded : (config layout).BoundedBy (200 * layout.width) (700 * layout.width + 200) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (scalar_bounded layout) (points_bounded layout)).mono
  all_goals have := layout.sizes; omega
theorem arguments_bounded : (arguments layout).BoundedBy (200 * layout.width) (700 * layout.width + 200) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (scalar_bounded layout) (generator_bounded layout)).mono
  all_goals have := layout.sizes; omega

variable [SMul F PK] (scale : Implementation .unit layout.arguments layout.key (fun value => value.1 • value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 5 < 2 ^ w)
    {scaleTime scaleWords : Nat} (scaleBound : scale.BoundedBy scaleTime scaleWords)
include scaleBound in
theorem signingKey_bounded : (signingKey layout scale).BoundedBy
    (scaleTime + 200 * layout.width) (scaleWords + 700 * layout.width + 201) := by
  apply ((arguments_bounded layout).then scaleBound).mono <;> omega
include scaleBound in
theorem computedKeys_bounded : (computedKeys layout scale scaleBuffers reserve).BoundedBy
    (scaleTime + 400 * layout.width) (scaleWords + 1400 * layout.width + 500) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (generator_bounded layout) (signingKey_bounded layout scale scaleBound)).mono
  all_goals have := layout.sizes; omega
include scaleBound in
theorem bounded : (implementation layout scale scaleBuffers reserve).BoundedBy
    (scaleTime + 800 * layout.width) (scaleWords + 3000 * layout.width + 1000) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (config_bounded layout)
    (computedKeys_bounded layout scale scaleBuffers reserve scaleBound)).mono
  all_goals have := layout.sizes; omega

variable {scaleSlots : Nat} (scaleNames : NamesAccounted scale.program.code scaleSlots)
include scaleNames in
theorem local_names : NamesAccounted (implementation layout scale scaleBuffers reserve).program.code scaleSlots := by
  have scalarNames : NamesAccounted (scalar layout).program.code scaleSlots := Implementation.first_names _ _ _ _ _
  have challengeNames : NamesAccounted (challenge layout).program.code scaleSlots := Implementation.second_names _ _ _ _ _
  have pointsNames : NamesAccounted (points layout).program.code scaleSlots :=
    challengeNames.seq (Implementation.first_names _ _ _ _ _)
  have generatorNames : NamesAccounted (generator layout).program.code scaleSlots :=
    (challengeNames.seq (Implementation.second_names _ _ _ _ _)).seq (Implementation.first_names _ _ _ _ _)
  have configNames : NamesAccounted (config layout).program.code scaleSlots :=
    Implementation.pair_names _ _ _ _ _ _ _ _ scalarNames pointsNames
  have argumentNames : NamesAccounted (arguments layout).program.code scaleSlots :=
    Implementation.pair_names _ _ _ _ _ _ _ _ scalarNames generatorNames
  have keysNames : NamesAccounted (computedKeys layout scale scaleBuffers reserve).program.code scaleSlots :=
    Implementation.pair_names _ _ _ _ _ _ _ _ generatorNames (argumentNames.seq scaleNames)
  exact Implementation.pair_names _ _ _ _ _ _ _ _ configNames keysNames

variable (port : Interactive.Port w unifSpec) (draw : Interactive.Code w)
    (source : ProbComp layout.scalar.Value)
    (drawCorrect : Interactive.Refines port .unit layout.unit.representation layout.scalar.representation (fun _ => source) draw)
    {drawTime drawWords : Nat}
    (drawTimeBound : Interactive.TimeBound port .unit layout.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords)

def timeBudget (drawTime scaleTime : Nat) : Nat := drawTime + scaleTime + 820 * layout.width
def codeBudget (drawWords scaleWords : Nat) : Nat := drawWords + scaleWords + 3100 * layout.width + 1100

omit [SMul F PK] in
include drawCorrect drawTimeBound in
theorem sample_time : Interactive.TimeBound port .unit layout.challenge.representation (sample layout port draw)
    (drawTime + 8 * layout.scalar.representation.encoding.words + 12 * layout.challenge.representation.encoding.words) := by
  have saved := drawTimeBound.retain drawCorrect (by decide) layout.challenge.representation layout.wordFits
    (by change 0 + layout.challenge.representation.encoding.words < 2 ^ w; simpa only [Nat.zero_add] using layout.challenge.representation.fits)
  have viewed := saved.viewInput layout.challenge.representation (fun value => (⟨(), trivial⟩, value)) (fun _ => rfl)
  exact viewed.mono (Interactive.retain_time_unit_le _ 0 _ _ _)

include drawCorrect drawTimeBound scaleBound in
theorem time : Interactive.TimeBound port .unit layout.challenge.representation (code layout scale scaleBuffers reserve port draw)
    (timeBudget layout drawTime scaleTime) := by
  have localBound := Interactive.TimeBound.compute (port := port) (cost := .unit)
    (implementation layout scale scaleBuffers reserve).program _ (bounded layout scale scaleBuffers reserve scaleBound).time_le
  apply ((sample_time layout port draw source drawCorrect drawTimeBound).seq
    (sample_refines layout port draw source drawCorrect) localBound).mono
  have := layout.sizes
  unfold timeBudget
  omega
include drawWordsBound scaleBound in
theorem words : ((code layout scale scaleBuffers reserve port draw).lower port).descriptionWords ≤ codeBudget layout drawWords scaleWords := by
  have retained := Interactive.retain_descriptionWords_le port draw (Interactive.savedBuffer port draw) 0
    layout.scalar.representation.encoding.words layout.challenge.representation.encoding.words
  have localBound := (bounded layout scale scaleBuffers reserve scaleBound).code_le
  change ((sample layout port draw).lower port).descriptionWords ≤ _ at retained
  have := layout.sizes
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

include scaleNames in
theorem names {drawSlots : Nat} (drawNames : WordIO.NamesBound (draw.lower port) drawSlots) :
    WordIO.NamesAccounted ((code layout scale scaleBuffers reserve port draw).lower port)
      (max (max 3 drawSlots) scaleSlots) := by
  have saved := Interactive.retain_names port drawNames.accounted 0
    layout.scalar.representation.encoding.words layout.challenge.representation.encoding.words
  have localNames := WordIO.NamesAccounted.compute (local_names layout scale scaleBuffers reserve scaleNames)
  exact (saved.mono (by omega)).seq (localNames.mono (by omega))

theorem descriptionFits {drawSlots : Nat} (drawFits : (draw.lower port).DescriptionFits)
    (drawNames : WordIO.NamesBound (draw.lower port) drawSlots) (drawReserve : drawSlots < 2 ^ w) :
    ((code layout scale scaleBuffers reserve port draw).lower port).DescriptionFits := by
  have named : Interactive.savedBuffer port draw < 2 ^ w := by
    have bound := drawNames.buffers
    have width := layout.wordFits
    unfold Interactive.savedBuffer
    omega
  have sampled := Interactive.retain_descriptionFits port draw (Interactive.savedBuffer port draw) 0
    layout.scalar.representation.encoding.words layout.challenge.representation.encoding.words layout.wordFits
    drawFits named (by positivity) layout.challenge.representation.fits layout.sampled.representation.fits
  exact sampled.seq layout.wordFits (.compute (implementation layout scale scaleBuffers reserve).program.description_fits)
end Signatures.Runtime.CaliperBackend.WeightedBadSetup
