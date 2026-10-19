import Signatures.Runtime.Caliper.CoronService

/-! The co-CDH terminal frame and actual extraction arithmetic. The signature
and challenge point survive the cache read in an explicitly copied pair. The
returned scalar is selected from the paired entry; the coin and table are
discarded only after the cache read has executed. -/
namespace Signatures.Runtime.CaliperBackend.CoronTerminal
open Caliper BoundedSource
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G : Type}
    (layout : CoronService.Layouts w M F G randomBound qS)

def width : Nat := layout.service.cache.lookup.width + 4 * layout.point.representation.encoding.words

theorem fits_of_le {words : Nat} (bound : words ≤ 16 * width layout) : words < 2 ^ w :=
  layout.service.fits_of_le (bound.trans (by
    unfold width BLSReply.Layouts.width
    change 16 * (_ + 4 * layout.point.representation.encoding.words) ≤
      16 * (_ + (layout.point.representation.encoding.words +
        (layout.point.representation.encoding.words + layout.point.representation.encoding.words)) +
        layout.point.representation.encoding.words + _)
    omega))

theorem base_sizes :
    (CacheRead.output layout.service.cache).representation.encoding.words +
        layout.response.points.representation.encoding.words ≤ width layout ∧
      layout.cache.value.representation.encoding.words ≤ width layout ∧
      layout.service.cache.value.representation.encoding.words ≤ width layout ∧
      layout.point.representation.encoding.words ≤ width layout ∧
      layout.response.points.representation.encoding.words ≤ width layout := by
  have cacheWidth := layout.service.lookup_width
  change layout.service.cache.lookup.width = layout.cache.key.representation.encoding.words +
    (layout.cache.value.representation.encoding.words + 1) + layout.service.cache.lookup.table.representation.encoding.words at cacheWidth
  change (layout.cache.value.representation.encoding.words + 1 + layout.service.cache.lookup.table.representation.encoding.words) +
    (layout.point.representation.encoding.words + layout.point.representation.encoding.words) ≤ _ ∧ _ ∧ _ ∧ _ ∧ _
  change _ ∧ _ ∧ layout.cache.value.representation.encoding.words + 1 ≤ _ ∧ _ ∧
    layout.point.representation.encoding.words + layout.point.representation.encoding.words ≤ _
  unfold width
  omega

def returned : Layout w (((F × Fin (qS.val + 1)) × List (M × (F × Fin (qS.val + 1)))) × (G × G)) :=
  (CacheRead.output layout.service.cache).prod layout.response.points
    (fits_of_le layout ((base_sizes layout).1.trans (by omega)))
theorem returned_le : (returned layout).representation.encoding.words ≤ width layout := (base_sizes layout).1

def sampled : Implementation .unit (returned layout) layout.service.cache.value (fun value => value.1.1) :=
  (Implementation.first (by decide) (CacheRead.output layout.service.cache) layout.response.points layout.cache.wordFits _).then
    (Implementation.first (by decide) layout.service.cache.value layout.service.cache.lookup.table layout.cache.wordFits _)
def scalar : Implementation .unit (returned layout) layout.cache.value (fun value => value.1.1.1) :=
  (sampled layout).then (Implementation.first (by decide) layout.cache.value layout.response.coin layout.cache.wordFits _)
def saved : Implementation .unit (returned layout) layout.response.points Prod.snd :=
  Implementation.second (by decide) (CacheRead.output layout.service.cache) layout.response.points layout.cache.wordFits _
def signature : Implementation .unit (returned layout) layout.point (fun value => value.2.1) :=
  (saved layout).then (Implementation.first (by decide) layout.point layout.point layout.cache.wordFits _)
def challenge : Implementation .unit (returned layout) layout.point (fun value => value.2.2) :=
  (saved layout).then (Implementation.second (by decide) layout.point layout.point layout.cache.wordFits _)

theorem scalar_buffers : (scalar layout).program.code.memBound ≤ 2 :=
  max_le (max_le (Implementation.first_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _))
    (Implementation.first_buffers _ _ _ _ _)
theorem signature_buffers : (signature layout).program.code.memBound ≤ 2 :=
  max_le (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)
theorem challenge_buffers : (challenge layout).program.code.memBound ≤ 2 :=
  max_le (Implementation.second_buffers _ _ _ _ _ ) (Implementation.second_buffers _ _ _ _ _)

def operands : Implementation .unit (returned layout) layout.response.scaleArgs (fun value => (value.1.1.1, value.2.2)) :=
  (scalar layout).pair (challenge layout) (by decide) layout.cache.wordFits
    (layout.service.smallNameFits _ (scalar_buffers layout) (by decide))
    (layout.service.smallNameFits _ (challenge_buffers layout) (by decide))
    (fits_of_le layout (by have := returned_le layout; omega))
    (fits_of_le layout (by have := returned_le layout; have := base_sizes layout; omega)) _
theorem operands_buffers : (operands layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (scalar_buffers layout) (challenge_buffers layout)

variable [SMul F G]
    (scale : Implementation .unit layout.response.scaleArgs layout.point (fun value => value.1 • value.2))
def scaled : Implementation .unit (returned layout) layout.point (fun value => value.1.1.1 • value.2.2) :=
  (operands layout).then scale
variable {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 3 < 2 ^ w)
include scaleBuffers in
theorem scaled_buffers : (scaled layout scale).program.code.memBound ≤ max 3 slots :=
  max_le_max (operands_buffers layout) scaleBuffers
def subtractionArgs : Implementation .unit (returned layout) layout.response.points
    (fun value => (value.2.1, value.1.1.1 • value.2.2)) :=
  (signature layout).pair (scaled layout scale) (by decide) layout.cache.wordFits
    (layout.service.smallNameFits _ (signature_buffers layout) (by decide))
    (layout.service.nameFits _ (scaled_buffers layout scale scaleBuffers) (by have := layout.cache.wordFits; omega))
    (fits_of_le layout (by have := returned_le layout; omega))
    (fits_of_le layout (by have := returned_le layout; have := base_sizes layout; omega)) _
variable [Sub G] (sub : Implementation .unit layout.response.points layout.point (fun value => value.1 - value.2))
def extract : Implementation .unit (returned layout) layout.point (fun value => value.2.1 - value.1.1.1 • value.2.2) :=
  (subtractionArgs layout scale scaleBuffers reserve).then sub

end Signatures.Runtime.CaliperBackend.CoronTerminal
