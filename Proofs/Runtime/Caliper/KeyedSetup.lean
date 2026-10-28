import Proofs.Runtime.Caliper.WeightedSetup
import Proofs.Runtime.Caliper.SynchronizesObservations

/-! Executed sampling of a known key for a wrapped weighted reduction. The stage
keeps the configuration, draws a scalar `k`, and hands the caller the key pair
`(pk, k • g)` together with `k`: the second key's exponent is known, so a wrapper can
add its share of a signature. The output is a challenge of the shape the shared
initialized program consumes, with keys of type `(K × K) × F`. -/
namespace Signatures.Runtime.CaliperBackend.KeyedSetup
open Caliper BoundedSource OracleComp OracleSpec

structure Layouts (w : Nat) (F C K : Type) where
  scalar : Layout w F
  config : Layout w C
  key : Layout w K
  wordFits : 16 < 2 ^ w
  storageFits : 16 * (scalar.representation.encoding.words + config.representation.encoding.words +
    2 * key.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {F C K : Type} (layout : Layouts w F C K)
def width : Nat := layout.scalar.representation.encoding.words + layout.config.representation.encoding.words +
  2 * layout.key.representation.encoding.words
theorem fits {n : Nat} (bound : n ≤ 16 * layout.width) : n < 2 ^ w := bound.trans_lt layout.storageFits
def keys := layout.key.prod layout.key (layout.fits (by unfold width; omega))
def challenge := layout.config.prod layout.keys (layout.fits (by change _ + (_ + _) ≤ _; unfold width; omega))
def sampled := layout.scalar.prod layout.challenge (layout.fits (by change _ + (_ + (_ + _)) ≤ _; unfold width; omega))
def arguments := layout.scalar.prod layout.key (layout.fits (by unfold width; omega))
/-- The wrapped key: both public keys and the known exponent of the second. -/
def keyed := layout.keys.prod layout.scalar (layout.fits (by change (_ + _) + _ ≤ _; unfold width; omega))
def keyeds := layout.keyed.prod layout.keyed (layout.fits (by change ((_ + _) + _) + ((_ + _) + _) ≤ _; unfold width; omega))
def output := layout.config.prod layout.keyeds (layout.fits (by
  change _ + (((_ + _) + _) + ((_ + _) + _)) ≤ _; unfold width; omega))
def unit (_layout : Layouts w F C K) : Layout w Unit := DataImplementation.unitLayout w
theorem sizes : layout.scalar.representation.encoding.words ≤ layout.width ∧
    layout.config.representation.encoding.words ≤ layout.width ∧
    layout.key.representation.encoding.words ≤ layout.width ∧
    layout.keys.representation.encoding.words ≤ layout.width ∧
    layout.challenge.representation.encoding.words ≤ layout.width ∧
    layout.sampled.representation.encoding.words ≤ layout.width ∧
    layout.keyed.representation.encoding.words ≤ layout.width ∧
    layout.keyeds.representation.encoding.words ≤ 2 * layout.width ∧
    layout.output.representation.encoding.words ≤ 2 * layout.width := by
  change _ ∧ _ ∧ _ ∧ (_ + _) ≤ _ ∧ (_ + (_ + _)) ≤ _ ∧ (_ + (_ + (_ + _))) ≤ _ ∧ ((_ + _) + _) ≤ _ ∧
    (((_ + _) + _) + ((_ + _) + _)) ≤ _ ∧ (_ + (((_ + _) + _) + ((_ + _) + _))) ≤ _
  unfold width
  omega
include layout in
theorem nameFits {X Y : Type} {input : Layout w X} {output : Layout w Y} {f : X → Y}
    (body : Implementation .unit input output f) {slots : Nat}
    (bound : body.program.code.memBound ≤ slots) (room : slots < 2 ^ w) : body.program.savedBuffer < 2 ^ w := by
  have width := layout.wordFits
  change max 2 body.program.code.memBound < 2 ^ w
  omega
end Layouts

variable {w : Nat} {F C K : Type} (layout : Layouts w F C K)

def scalar : Implementation .unit layout.sampled layout.scalar Prod.fst :=
  Implementation.first (by decide) _ _ layout.wordFits _
def challenge : Implementation .unit layout.sampled layout.challenge Prod.snd :=
  Implementation.second (by decide) _ _ layout.wordFits _
def config : Implementation .unit layout.sampled layout.config (fun value => value.2.1) :=
  (challenge layout).then (Implementation.first (by decide) _ _ layout.wordFits _)
def keys : Implementation .unit layout.sampled layout.keys (fun value => value.2.2) :=
  (challenge layout).then (Implementation.second (by decide) _ _ layout.wordFits _)
def generator : Implementation .unit layout.sampled layout.key (fun value => value.2.2.1) :=
  (keys layout).then (Implementation.first (by decide) _ _ layout.wordFits _)
def publicKey : Implementation .unit layout.sampled layout.key (fun value => value.2.2.2) :=
  (keys layout).then (Implementation.second (by decide) _ _ layout.wordFits _)

theorem scalar_buffers : (scalar layout).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
theorem challenge_buffers : (challenge layout).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _
theorem config_buffers : (config layout).program.code.memBound ≤ 2 :=
  max_le (challenge_buffers layout) (Implementation.first_buffers _ _ _ _ _)
theorem keys_buffers : (keys layout).program.code.memBound ≤ 2 :=
  max_le (challenge_buffers layout) (Implementation.second_buffers _ _ _ _ _)
theorem generator_buffers : (generator layout).program.code.memBound ≤ 2 :=
  max_le (keys_buffers layout) (Implementation.first_buffers _ _ _ _ _)
theorem publicKey_buffers : (publicKey layout).program.code.memBound ≤ 2 :=
  max_le (keys_buffers layout) (Implementation.second_buffers _ _ _ _ _)

def arguments : Implementation .unit layout.sampled layout.arguments (fun value => (value.1, value.2.2.1)) :=
  (scalar layout).pair (generator layout) (by decide) layout.wordFits
    (layout.nameFits _ (scalar_buffers layout) (by have := layout.wordFits; omega))
    (layout.nameFits _ (generator_buffers layout) (by have := layout.wordFits; omega))
    (layout.fits (by have := layout.sizes; omega)) (layout.fits (by have := layout.sizes; omega)) _
theorem arguments_buffers : (arguments layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (scalar_buffers layout) (generator_buffers layout)

variable [SMul F K] (scale : Implementation .unit layout.arguments layout.key (fun value => value.1 • value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 5 < 2 ^ w)

/-- The second public key `k • g`. -/
def knownKey : Implementation .unit layout.sampled layout.key (fun value => value.1 • value.2.2.1) :=
  (arguments layout).then scale
include scaleBuffers in
theorem knownKey_buffers : (knownKey layout scale).program.code.memBound ≤ max 3 slots :=
  max_le_max (arguments_buffers layout) scaleBuffers

def pair : Implementation .unit layout.sampled layout.keys (fun value => (value.2.2.2, value.1 • value.2.2.1)) :=
  (publicKey layout).pair (knownKey layout scale) (by decide) layout.wordFits
    (layout.nameFits _ (publicKey_buffers layout) (by have := layout.wordFits; omega))
    (layout.nameFits _ (knownKey_buffers layout scale scaleBuffers) (by have := layout.wordFits; have := reserve; omega))
    (layout.fits (by have := layout.sizes; omega)) (layout.fits (by have := layout.sizes; omega)) _
theorem pair_buffers : (pair layout scale scaleBuffers reserve).program.code.memBound ≤ max 3 slots + 1 := by
  have bound : (pair layout scale scaleBuffers reserve).program.code.memBound ≤ max 2 (max 2 (max 3 slots)) + 1 :=
    Implementation.pair_buffers _ _ layout.wordFits _ _ _ _ _
      (publicKey_buffers layout) (knownKey_buffers layout scale scaleBuffers)
  apply bound.trans
  omega

def keyed : Implementation .unit layout.sampled layout.keyed (fun value => ((value.2.2.2, value.1 • value.2.2.1), value.1)) :=
  (pair layout scale scaleBuffers reserve).pair (scalar layout) (by decide) layout.wordFits
    (layout.nameFits _ (pair_buffers layout scale scaleBuffers reserve) (by have := layout.wordFits; have := reserve; omega))
    (layout.nameFits _ (scalar_buffers layout) (by have := layout.wordFits; omega))
    (layout.fits (by have := layout.sizes; omega)) (layout.fits (by have := layout.sizes; omega)) _
theorem keyed_buffers : (keyed layout scale scaleBuffers reserve).program.code.memBound ≤ max 3 slots + 2 := by
  have bound : (keyed layout scale scaleBuffers reserve).program.code.memBound ≤ max 2 (max (max 3 slots + 1) 2) + 1 :=
    Implementation.pair_buffers _ _ layout.wordFits _ _ _ _ _
      (pair_buffers layout scale scaleBuffers reserve) (scalar_buffers layout)
  apply bound.trans
  omega

/-- The wrapped key, in both key positions of the output challenge. -/
def keyeds : Implementation .unit layout.sampled layout.keyeds
    (fun value => (((value.2.2.2, value.1 • value.2.2.1), value.1), ((value.2.2.2, value.1 • value.2.2.1), value.1))) :=
  (keyed layout scale scaleBuffers reserve).pair (keyed layout scale scaleBuffers reserve) (by decide) layout.wordFits
    (layout.nameFits _ (keyed_buffers layout scale scaleBuffers reserve) (by have := layout.wordFits; have := reserve; omega))
    (layout.nameFits _ (keyed_buffers layout scale scaleBuffers reserve) (by have := layout.wordFits; have := reserve; omega))
    (layout.fits (by have := layout.sizes; omega)) (layout.fits (by have := layout.sizes; omega)) _
theorem keyeds_buffers : (keyeds layout scale scaleBuffers reserve).program.code.memBound ≤ max 3 slots + 3 := by
  have bound : (keyeds layout scale scaleBuffers reserve).program.code.memBound ≤ max 2 (max (max 3 slots + 2) (max 3 slots + 2)) + 1 :=
    Implementation.pair_buffers _ _ layout.wordFits _ _ _ _ _
      (keyed_buffers layout scale scaleBuffers reserve) (keyed_buffers layout scale scaleBuffers reserve)
  apply bound.trans
  omega

/-- The sampled value and original challenge, laid out as the keyed challenge. -/
def value (sampled : F × (C × (K × K))) : C × (((K × K) × F) × ((K × K) × F)) :=
  (sampled.2.1, (((sampled.2.2.2, sampled.1 • sampled.2.2.1), sampled.1), ((sampled.2.2.2, sampled.1 • sampled.2.2.1), sampled.1)))

def implementation : Implementation .unit layout.sampled layout.output (value (F := F) (C := C) (K := K)) :=
  (config layout).pair (keyeds layout scale scaleBuffers reserve) (by decide) layout.wordFits
    (layout.nameFits _ (config_buffers layout) (by have := layout.wordFits; omega))
    (layout.nameFits _ (keyeds_buffers layout scale scaleBuffers reserve) (by have := layout.wordFits; have := reserve; omega))
    (layout.fits (by have := layout.sizes; omega)) (layout.fits (by have := layout.sizes; omega)) _
theorem buffers : (implementation layout scale scaleBuffers reserve).program.code.memBound ≤ max 3 slots + 4 := by
  have bound : (implementation layout scale scaleBuffers reserve).program.code.memBound ≤ max 2 (max 2 (max 3 slots + 3)) + 1 :=
    Implementation.pair_buffers _ _ layout.wordFits _ _ _ _ _
      (config_buffers layout) (keyeds_buffers layout scale scaleBuffers reserve)
  apply bound.trans
  omega

variable (port : Interactive.Port w unifSpec) (draw : Interactive.Code w)
    (source : ProbComp layout.scalar.Value)

def sample : Interactive.Code w :=
  Interactive.retain draw (Interactive.savedBuffer port draw) 0
    layout.scalar.representation.encoding.words layout.challenge.representation.encoding.words
def sampledValue (value : layout.challenge.Value) (scalar : layout.scalar.Value) : layout.sampled.Value :=
  ⟨(scalar.val, value.val), scalar.property, value.property⟩

variable (drawCorrect : Interactive.Refines port .unit layout.unit.representation layout.scalar.representation (fun _ => source) draw)

omit [SMul F K] in
include drawCorrect in
theorem sample_refines : Interactive.Refines port .unit layout.challenge.representation layout.sampled.representation
    (fun value => sampledValue layout value <$> source) (sample layout port draw) := by
  have saved := drawCorrect.retain (by decide) layout.challenge.representation layout.wordFits
    (by change 0 + layout.challenge.representation.encoding.words < 2 ^ w; simpa only [Nat.zero_add] using layout.challenge.representation.fits)
    layout.sampled.representation.fits
  have input := saved.viewInput layout.challenge.representation (fun value => (⟨(), trivial⟩, value)) (fun _ => rfl)
  have output := input.viewOutput layout.sampled.representation
    (fun value => ⟨(value.1.val, value.2.val), value.1.property, value.2.property⟩) (fun _ => rfl)
  simp only [Functor.map_map] at output
  convert output using 1
  · funext value; rfl
  · rfl

def code : Interactive.Code w :=
  .seq (sample layout port draw) (.compute (implementation layout scale scaleBuffers reserve).program.code)
def result (sampled : layout.sampled.Value) : layout.output.Value :=
  ⟨value sampled.val, (implementation layout scale scaleBuffers reserve).preserves sampled.val sampled.property⟩
def denote (challenge : layout.challenge.Value) : ProbComp layout.output.Value :=
  (fun scalar => result layout scale scaleBuffers reserve (sampledValue layout challenge scalar)) <$> source

include drawCorrect in
theorem refines : Interactive.Refines port .unit layout.challenge.representation layout.output.representation
    (denote layout scale scaleBuffers reserve source) (code layout scale scaleBuffers reserve port draw) := by
  have composed := (sample_refines layout port draw source drawCorrect).seq
    (Interactive.Refines.compute port .unit (implementation layout scale scaleBuffers reserve).program)
  simp only [bind_pure_comp, Functor.map_map] at composed
  convert composed using 1
  · funext value; rfl
  · rfl

variable [SampleableType F] (uniform : Subtype.val <$> source = ($ᵗ F : ProbComp F))
include uniform in
theorem denote_uniform (challenge : layout.challenge.Value) :
    Subtype.val <$> denote layout scale scaleBuffers reserve source challenge =
      (fun scalar => value (scalar, challenge.val)) <$> ($ᵗ F : ProbComp F) := by
  rw [← uniform]
  simp only [denote, Functor.map_map]
  rfl

end Signatures.Runtime.CaliperBackend.KeyedSetup
