import Proofs.Runtime.Caliper.KeyedSetup

/-! Bounds for the executed known-key draw, retained challenge and wrapped key pair.
Only the sampler and the key-scaling routine supply primitive budgets. -/
namespace Signatures.Runtime.CaliperBackend.KeyedSetup
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {F C K : Type} (layout : Layouts w F C K)

theorem scalar_bounded : (scalar layout).BoundedBy (8 * layout.scalar.representation.encoding.words)
    (26 * layout.scalar.representation.encoding.words + 14) := Implementation.first_boundedBy _ _ _ _
theorem config_bounded : (config layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals have := layout.sizes; dsimp only [Layouts.challenge, Layouts.keys] at this ⊢; omega
theorem keys_bounded : (keys layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals have := layout.sizes; dsimp only [Layouts.challenge, Layouts.keys] at this ⊢; omega
theorem generator_bounded : (generator layout).BoundedBy (24 * layout.width) (78 * layout.width + 44) := by
  apply (((Implementation.second_boundedBy _ _ _ _).then (Implementation.second_boundedBy _ _ _ _)).then
    (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals have := layout.sizes; dsimp only [Layouts.challenge, Layouts.keys] at this ⊢; omega
theorem publicKey_bounded : (publicKey layout).BoundedBy (24 * layout.width) (78 * layout.width + 44) := by
  apply (((Implementation.second_boundedBy _ _ _ _).then (Implementation.second_boundedBy _ _ _ _)).then
    (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals have := layout.sizes; dsimp only [Layouts.challenge, Layouts.keys] at this ⊢; omega
theorem arguments_bounded : (arguments layout).BoundedBy (200 * layout.width) (700 * layout.width + 200) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (scalar_bounded layout) (generator_bounded layout)).mono
  all_goals have := layout.sizes; omega

variable [SMul F K] (scale : Implementation .unit layout.arguments layout.key (fun value => value.1 • value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 5 < 2 ^ w)
    {scaleTime scaleWords : Nat} (scaleBound : scale.BoundedBy scaleTime scaleWords)

include scaleBound in
theorem knownKey_bounded : (knownKey layout scale).BoundedBy
    (scaleTime + 200 * layout.width) (scaleWords + 700 * layout.width + 201) := by
  apply ((arguments_bounded layout).then scaleBound).mono <;> omega
include scaleBound in
theorem pair_bounded : (pair layout scale scaleBuffers reserve).BoundedBy
    (scaleTime + 400 * layout.width) (scaleWords + 1400 * layout.width + 500) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (publicKey_bounded layout) (knownKey_bounded layout scale scaleBound)).mono
  all_goals have := layout.sizes; omega
include scaleBound in
theorem keyed_bounded : (keyed layout scale scaleBuffers reserve).BoundedBy
    (scaleTime + 600 * layout.width) (scaleWords + 2000 * layout.width + 700) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (pair_bounded layout scale scaleBuffers reserve scaleBound) (scalar_bounded layout)).mono
  all_goals have := layout.sizes; omega
include scaleBound in
theorem keyeds_bounded : (keyeds layout scale scaleBuffers reserve).BoundedBy
    (2 * scaleTime + 1400 * layout.width) (2 * scaleWords + 4500 * layout.width + 1600) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (keyed_bounded layout scale scaleBuffers reserve scaleBound)
    (keyed_bounded layout scale scaleBuffers reserve scaleBound)).mono
  all_goals have := layout.sizes; omega
include scaleBound in
theorem bounded : (implementation layout scale scaleBuffers reserve).BoundedBy
    (2 * scaleTime + 1600 * layout.width) (2 * scaleWords + 5000 * layout.width + 1800) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (config_bounded layout)
    (keyeds_bounded layout scale scaleBuffers reserve scaleBound)).mono
  all_goals have := layout.sizes; omega

variable {scaleSlots : Nat} (scaleNames : NamesAccounted scale.program.code scaleSlots)
include scaleNames in
theorem local_names : NamesAccounted (implementation layout scale scaleBuffers reserve).program.code scaleSlots := by
  have scalarNames : NamesAccounted (scalar layout).program.code scaleSlots := Implementation.first_names _ _ _ _ _
  have challengeNames : NamesAccounted (challenge layout).program.code scaleSlots := Implementation.second_names _ _ _ _ _
  have configNames : NamesAccounted (config layout).program.code scaleSlots :=
    challengeNames.seq (Implementation.first_names _ _ _ _ _)
  have keysNames : NamesAccounted (keys layout).program.code scaleSlots :=
    challengeNames.seq (Implementation.second_names _ _ _ _ _)
  have generatorNames : NamesAccounted (generator layout).program.code scaleSlots :=
    keysNames.seq (Implementation.first_names _ _ _ _ _)
  have publicKeyNames : NamesAccounted (publicKey layout).program.code scaleSlots :=
    keysNames.seq (Implementation.second_names _ _ _ _ _)
  have argumentNames : NamesAccounted (arguments layout).program.code scaleSlots :=
    Implementation.pair_names _ _ _ _ _ _ _ _ scalarNames generatorNames
  have pairNames : NamesAccounted (pair layout scale scaleBuffers reserve).program.code scaleSlots :=
    Implementation.pair_names _ _ _ _ _ _ _ _ publicKeyNames (argumentNames.seq scaleNames)
  have keyedNames : NamesAccounted (keyed layout scale scaleBuffers reserve).program.code scaleSlots :=
    Implementation.pair_names _ _ _ _ _ _ _ _ pairNames scalarNames
  have keyedsNames : NamesAccounted (keyeds layout scale scaleBuffers reserve).program.code scaleSlots :=
    Implementation.pair_names _ _ _ _ _ _ _ _ keyedNames keyedNames
  exact Implementation.pair_names _ _ _ _ _ _ _ _ configNames keyedsNames

variable (port : Interactive.Port w unifSpec) (draw : Interactive.Code w)
    (source : ProbComp layout.scalar.Value)
    (drawCorrect : Interactive.Refines port .unit layout.unit.representation layout.scalar.representation (fun _ => source) draw)
    {drawTime drawWords : Nat}
    (drawTimeBound : Interactive.TimeBound port .unit layout.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords)

def timeBudget (drawTime scaleTime : Nat) : Nat := drawTime + 2 * scaleTime + 1700 * layout.width
def codeBudget (drawWords scaleWords : Nat) : Nat := drawWords + 2 * scaleWords + 5200 * layout.width + 2000

omit [SMul F K] in
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

end Signatures.Runtime.CaliperBackend.KeyedSetup
