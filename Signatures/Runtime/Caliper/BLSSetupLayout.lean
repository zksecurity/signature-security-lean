import Signatures.Runtime.Caliper.BLSInitialization

/-! Runtime challenge layouts for both BLS AGM reductions. The public key and
challenge points are input data. The bad branch also stores its sampled scalar.
One explicit address bound covers all generated setup frames. -/

namespace Signatures.Runtime.CaliperBackend.BLSSetup
open Caliper BoundedSource

structure Layouts (w : Nat) (M F G K : Type) where
  scheme : BLSReply.SchemeLayouts w M F G
  key : Layout w K
  storageFits : 16 * (scheme.good.store.representation.encoding.words + scheme.bad.store.representation.encoding.words +
    2 * key.representation.encoding.words + 2 * scheme.cache.value.representation.encoding.words +
    4 * scheme.point.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {M F G K : Type} (layout : Layouts w M F G K)

def width : Nat := layout.scheme.good.store.representation.encoding.words + layout.scheme.bad.store.representation.encoding.words +
  2 * layout.key.representation.encoding.words + 2 * layout.scheme.cache.value.representation.encoding.words +
  4 * layout.scheme.point.representation.encoding.words

theorem fits_of_le {words : Nat} (bound : words ≤ 16 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits

def keys : Layout w (K × K) := layout.key.prod layout.key (layout.fits_of_le (by dsimp only [width]; omega))
def challenge : Layout w ((G × G) × (K × K)) := layout.scheme.response.points.prod layout.keys (layout.fits_of_le (by
  change (layout.scheme.point.representation.encoding.words + layout.scheme.point.representation.encoding.words) +
    (layout.key.representation.encoding.words + layout.key.representation.encoding.words) ≤ _
  dsimp only [width]; omega))
def sampled : Layout w (F × ((G × G) × (K × K))) := layout.scheme.cache.value.prod layout.challenge (layout.fits_of_le (by
  change layout.scheme.cache.value.representation.encoding.words +
    ((layout.scheme.point.representation.encoding.words + layout.scheme.point.representation.encoding.words) +
      (layout.key.representation.encoding.words + layout.key.representation.encoding.words)) ≤ _
  dsimp only [width]; omega))
def scaleArgs : Layout w (F × K) := layout.scheme.cache.value.prod layout.key (layout.fits_of_le (by dsimp only [width]; omega))

theorem goodFits : layout.key.representation.encoding.words + layout.scheme.good.store.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by dsimp only [width]; omega)
theorem badFits : layout.key.representation.encoding.words + layout.scheme.bad.store.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by dsimp only [width]; omega)

def goodPrefix := BLSInitialization.sourceInput layout.scheme.good layout.key layout.goodFits
def badPrefix := BLSInitialization.sourceInput layout.scheme.bad layout.key layout.badFits
def goodOutput := BLSInitialization.sourceOutput layout.scheme.good layout.key layout.goodFits
def badOutput := BLSInitialization.sourceOutput layout.scheme.bad layout.key layout.badFits

@[simp] theorem keys_words : layout.keys.representation.encoding.words = 2 * layout.key.representation.encoding.words := by
  change _ + _ = _; omega
@[simp] theorem challenge_words : layout.challenge.representation.encoding.words =
    2 * layout.scheme.point.representation.encoding.words + 2 * layout.key.representation.encoding.words := by
  change (_ + _) + (_ + _) = _; dsimp only [BLSReply.SchemeLayouts.response]; omega
@[simp] theorem sampled_words : layout.sampled.representation.encoding.words =
    layout.scheme.cache.value.representation.encoding.words + 2 * layout.scheme.point.representation.encoding.words +
      2 * layout.key.representation.encoding.words := by
  change _ + ((_ + _) + (_ + _)) = _; dsimp only [BLSReply.SchemeLayouts.response]; omega
@[simp] theorem scaleArgs_words : layout.scaleArgs.representation.encoding.words =
    layout.scheme.cache.value.representation.encoding.words + layout.key.representation.encoding.words := rfl
@[simp] theorem goodPrefix_words : layout.goodPrefix.representation.encoding.words =
    layout.key.representation.encoding.words + 2 * layout.scheme.point.representation.encoding.words := by
  change _ + (_ + _) = _; dsimp only [BLSReply.SchemeLayouts.response]; omega
@[simp] theorem badPrefix_words : layout.badPrefix.representation.encoding.words =
    layout.key.representation.encoding.words + layout.scheme.cache.value.representation.encoding.words +
      2 * layout.scheme.point.representation.encoding.words := by
  change _ + (_ + (_ + _)) = _; dsimp only [BLSReply.SchemeLayouts.response]; omega

theorem sizes : layout.key.representation.encoding.words ≤ layout.width ∧
    layout.scheme.cache.value.representation.encoding.words ≤ layout.width ∧
    layout.scheme.response.points.representation.encoding.words ≤ layout.width ∧
    layout.challenge.representation.encoding.words ≤ layout.width ∧
    layout.sampled.representation.encoding.words ≤ layout.width ∧
    layout.scheme.bad.config.representation.encoding.words ≤ layout.width ∧
    layout.goodOutput.representation.encoding.words ≤ layout.width ∧
    layout.badOutput.representation.encoding.words ≤ layout.width := by
  rw [challenge_words, sampled_words]
  change _ ∧ _ ∧ (_ + _) ≤ _ ∧ _ ∧ _ ∧ (_ + (_ + _)) ≤ _ ∧
    (layout.key.representation.encoding.words + layout.scheme.good.store.representation.encoding.words) ≤ _ ∧
    (layout.key.representation.encoding.words + layout.scheme.bad.store.representation.encoding.words) ≤ _
  dsimp only [BLSReply.SchemeLayouts.response, width]
  omega

include layout in
theorem nameFits {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (body : Implementation .unit input output f) {slots : Nat}
    (bound : body.program.code.memBound ≤ slots) (fits : slots < 2 ^ w) : body.program.savedBuffer < 2 ^ w := by
  have hw := layout.scheme.cache.wordFits
  change max 2 body.program.code.memBound < 2 ^ w
  omega

end Layouts

variable {w : Nat} {M F G K : Type} (layout : Layouts w M F G K)

def points : Implementation .unit layout.challenge layout.scheme.response.points Prod.fst :=
  Implementation.first (by decide) _ _ layout.scheme.cache.wordFits _
def keys : Implementation .unit layout.challenge layout.keys Prod.snd :=
  Implementation.second (by decide) _ _ layout.scheme.cache.wordFits _
def publicKey : Implementation .unit layout.challenge layout.key (fun value => value.2.2) :=
  (keys layout).then (Implementation.second (by decide) _ _ layout.scheme.cache.wordFits _)
def generator : Implementation .unit layout.challenge layout.key (fun value => value.2.1) :=
  (keys layout).then (Implementation.first (by decide) _ _ layout.scheme.cache.wordFits _)
def scalar : Implementation .unit layout.sampled layout.scheme.cache.value Prod.fst :=
  Implementation.first (by decide) _ _ layout.scheme.cache.wordFits _
def challenge : Implementation .unit layout.sampled layout.challenge Prod.snd :=
  Implementation.second (by decide) _ _ layout.scheme.cache.wordFits _
def sampledPoints : Implementation .unit layout.sampled layout.scheme.response.points (fun value => value.2.1) :=
  (challenge layout).then (points layout)
def sampledGenerator : Implementation .unit layout.sampled layout.key (fun value => value.2.2.1) :=
  (challenge layout).then (generator layout)

theorem points_buffers : (points layout).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
theorem keys_buffers : (keys layout).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _
theorem publicKey_buffers : (publicKey layout).program.code.memBound ≤ 2 :=
  max_le (keys_buffers layout) (Implementation.second_buffers _ _ _ _ _)
theorem generator_buffers : (generator layout).program.code.memBound ≤ 2 :=
  max_le (keys_buffers layout) (Implementation.first_buffers _ _ _ _ _)
theorem scalar_buffers : (scalar layout).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
theorem challenge_buffers : (challenge layout).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _
theorem sampledPoints_buffers : (sampledPoints layout).program.code.memBound ≤ 2 :=
  max_le (challenge_buffers layout) (points_buffers layout)
theorem sampledGenerator_buffers : (sampledGenerator layout).program.code.memBound ≤ 2 :=
  max_le (challenge_buffers layout) (generator_buffers layout)

def goodPrefix : Implementation .unit layout.challenge layout.goodPrefix (fun value => (value.2.2, value.1)) :=
  (publicKey layout).pair (points layout) (by decide) layout.scheme.cache.wordFits
    (layout.nameFits _ (publicKey_buffers layout) (by have := layout.scheme.cache.wordFits; omega))
    (layout.nameFits _ (points_buffers layout) (by have := layout.scheme.cache.wordFits; omega))
    (layout.fits_of_le (by rw [Layouts.challenge_words]; dsimp only [Layouts.width]; omega))
    (layout.fits_of_le (by rw [Layouts.challenge_words]; dsimp only [Layouts.width]; omega)) _

def config : Implementation .unit layout.sampled layout.scheme.bad.config (fun value => (value.1, value.2.1)) :=
  (scalar layout).pair (sampledPoints layout) (by decide) layout.scheme.cache.wordFits
    (layout.nameFits _ (scalar_buffers layout) (by have := layout.scheme.cache.wordFits; omega))
    (layout.nameFits _ (sampledPoints_buffers layout) (by have := layout.scheme.cache.wordFits; omega))
    (layout.fits_of_le (by rw [Layouts.sampled_words]; dsimp only [Layouts.width]; omega))
    (layout.fits_of_le (by rw [Layouts.sampled_words]; dsimp only [Layouts.width]; omega)) _

def arguments : Implementation .unit layout.sampled layout.scaleArgs (fun value => (value.1, value.2.2.1)) :=
  (scalar layout).pair (sampledGenerator layout) (by decide) layout.scheme.cache.wordFits
    (layout.nameFits _ (scalar_buffers layout) (by have := layout.scheme.cache.wordFits; omega))
    (layout.nameFits _ (sampledGenerator_buffers layout) (by have := layout.scheme.cache.wordFits; omega))
    (layout.fits_of_le (by rw [Layouts.sampled_words]; dsimp only [Layouts.width]; omega))
    (layout.fits_of_le (by rw [Layouts.sampled_words]; dsimp only [Layouts.width]; omega)) _

theorem goodPrefix_buffers : (goodPrefix layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (publicKey_buffers layout) (points_buffers layout)
theorem config_buffers : (config layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (scalar_buffers layout) (sampledPoints_buffers layout)
theorem arguments_buffers : (arguments layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (scalar_buffers layout) (sampledGenerator_buffers layout)

end Signatures.Runtime.CaliperBackend.BLSSetup
