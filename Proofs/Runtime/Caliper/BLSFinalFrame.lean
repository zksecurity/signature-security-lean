import Proofs.Runtime.Caliper.CacheTargetFrameNames
import Proofs.Runtime.Caliper.BLSPrivateAccumulateLayout

/-! BLS final-request construction from the signature evaluation result and
saved forgery data. The good branch executes the missing beta + hashes addition;
the bad branch keeps the saved beta while packing the pair-valued result. -/
namespace Signatures.Runtime.CaliperBackend.BLSFinalFrame
open Caliper BoundedSource
variable {w : Nat} {M F : Type} (layout : BLSPrivateAccumulate.Layouts w M F)

def context : Layout w (M × (F × F)) := layout.cache.key.prod layout.arithmetic.pair
  (layout.good.fits_of_le (by
    rw [BLSAccumulate.Layouts.pair_words]
    have := CacheTargetFrame.key_size layout.good
    have := layout.good.base_sizes
    change layout.cache.key.representation.encoding.words + 2 * layout.cache.value.representation.encoding.words ≤ _
    dsimp only [BLSPrivateAccumulate.Layouts.good, BLSPrivateAccumulate.Layouts.arithmetic, BLSAccumulate.Layouts.arithmetic, BLSResponse.Layouts.points] at *; omega))
def returned : Layout w ((F × List (M × F)) × (M × (F × F))) :=
  (CacheRead.output layout.cache).prod (context layout)
    (layout.good.fits_of_le (by
      change (_ + _) + (_ + (_ + _)) ≤ _
      dsimp only [CacheAccumulate.Layouts.width]
      rw [layout.good.cache_width]
      change _ ≤ 16 * (layout.cache.key.representation.encoding.words + layout.cache.value.representation.encoding.words +
        layout.cache.lookup.table.representation.encoding.words + layout.cache.value.representation.encoding.words +
        layout.cache.value.representation.encoding.words)
      dsimp only [BLSPrivateAccumulate.Layouts.good, BLSPrivateAccumulate.Layouts.arithmetic, BLSAccumulate.Layouts.arithmetic, BLSResponse.Layouts.points] at *; omega))
theorem sizes : (context layout).representation.encoding.words ≤ layout.good.width ∧
    (returned layout).representation.encoding.words ≤ layout.good.width ∧
    layout.arithmetic.pair.representation.encoding.words ≤ layout.good.width := by
  change (layout.cache.key.representation.encoding.words + (layout.cache.value.representation.encoding.words +
    layout.cache.value.representation.encoding.words)) ≤ layout.good.width ∧
    ((layout.cache.value.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words) +
      (layout.cache.key.representation.encoding.words + (layout.cache.value.representation.encoding.words +
        layout.cache.value.representation.encoding.words))) ≤ layout.good.width ∧
    (layout.cache.value.representation.encoding.words + layout.cache.value.representation.encoding.words) ≤ layout.good.width
  dsimp only [CacheAccumulate.Layouts.width]
  rw [layout.good.cache_width]
  change _ ∧ _ ∧ _ ≤ layout.cache.key.representation.encoding.words + layout.cache.value.representation.encoding.words +
    layout.cache.lookup.table.representation.encoding.words + layout.cache.value.representation.encoding.words +
    layout.cache.value.representation.encoding.words
  dsimp only [BLSPrivateAccumulate.Layouts.good, BLSPrivateAccumulate.Layouts.arithmetic, BLSAccumulate.Layouts.arithmetic, BLSResponse.Layouts.points] at *; omega
def target : Implementation .unit (returned layout) layout.cache.key (fun value => value.2.1) :=
  (Implementation.second (by decide) (CacheRead.output layout.cache) (context layout) layout.cache.wordFits _).then
    (Implementation.first (by decide) layout.cache.key layout.arithmetic.pair layout.cache.wordFits _)
def operands : Implementation .unit (returned layout) layout.arithmetic.pair (fun value => value.2.2) :=
  (Implementation.second (by decide) (CacheRead.output layout.cache) (context layout) layout.cache.wordFits _).then
    (Implementation.second (by decide) layout.cache.key layout.arithmetic.pair layout.cache.wordFits _)
def evaluated : Implementation .unit (returned layout) (CacheRead.output layout.cache) Prod.fst :=
  Implementation.first (by decide) (CacheRead.output layout.cache) (context layout) layout.cache.wordFits _
theorem target_buffers : (target layout).program.code.memBound ≤ 2 := max_le (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)
theorem operands_buffers : (operands layout).program.code.memBound ≤ 2 := max_le (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _)
theorem evaluated_buffers : (evaluated layout).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _

variable [Add F] (add : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 + value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)
def numerator : Implementation .unit (returned layout) layout.cache.value (fun value => value.2.2.1 + value.2.2.2) :=
  (operands layout).then add
include addBuffers in
theorem numerator_buffers : (numerator layout add).program.code.memBound ≤ max 2 slots := max_le_max (operands_buffers layout) addBuffers
def saved : Implementation .unit (returned layout) (CacheTargetFrame.context layout.good)
    (fun value => (value.2.1, value.2.2.1 + value.2.2.2)) :=
  (target layout).pair (numerator layout add) (by decide) layout.cache.wordFits
    (CacheAccumulate.nameFits layout.good _ (target_buffers layout) (by have := layout.cache.wordFits; dsimp only [BLSPrivateAccumulate.Layouts.good, BLSPrivateAccumulate.Layouts.arithmetic, BLSAccumulate.Layouts.arithmetic, BLSResponse.Layouts.points] at *; omega))
    (CacheAccumulate.nameFits layout.good _ (numerator_buffers layout add addBuffers) (by have := layout.cache.wordFits; dsimp only [BLSPrivateAccumulate.Layouts.good, BLSPrivateAccumulate.Layouts.arithmetic, BLSAccumulate.Layouts.arithmetic, BLSResponse.Layouts.points] at *; omega))
    (layout.good.fits_of_le (by have := sizes layout; dsimp only [BLSPrivateAccumulate.Layouts.good, BLSPrivateAccumulate.Layouts.arithmetic, BLSAccumulate.Layouts.arithmetic, BLSResponse.Layouts.points] at *; omega))
    (layout.good.fits_of_le (by have := sizes layout; have := CacheTargetFrame.key_size layout.good; dsimp only [BLSPrivateAccumulate.Layouts.good, BLSPrivateAccumulate.Layouts.arithmetic, BLSAccumulate.Layouts.arithmetic, BLSResponse.Layouts.points] at *; omega)) _
theorem saved_buffers : (saved layout add addBuffers reserve).program.code.memBound ≤ max 2 slots + 1 :=
  (Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := max 2 slots) _ _ _ _ _ _ _ _
    (target_buffers layout) (numerator_buffers layout add addBuffers)).trans (by dsimp only [BLSPrivateAccumulate.Layouts.good, BLSPrivateAccumulate.Layouts.arithmetic, BLSAccumulate.Layouts.arithmetic, BLSResponse.Layouts.points] at *; omega)
def normalize : Implementation .unit (returned layout) (CacheTargetFrame.returned layout.good)
    (fun value => (value.1, value.2.1, value.2.2.1 + value.2.2.2)) :=
  (evaluated layout).pair (saved layout add addBuffers reserve) (by decide) layout.cache.wordFits
    (CacheAccumulate.nameFits layout.good _ (evaluated_buffers layout) (by have := layout.cache.wordFits; dsimp only [BLSPrivateAccumulate.Layouts.good, BLSPrivateAccumulate.Layouts.arithmetic, BLSAccumulate.Layouts.arithmetic, BLSResponse.Layouts.points] at *; omega))
    (CacheAccumulate.nameFits layout.good _ (saved_buffers layout add addBuffers reserve) (by have := layout.cache.wordFits; dsimp only [BLSPrivateAccumulate.Layouts.good, BLSPrivateAccumulate.Layouts.arithmetic, BLSAccumulate.Layouts.arithmetic, BLSResponse.Layouts.points] at *; omega))
    (layout.good.fits_of_le (by have := sizes layout; dsimp only [BLSPrivateAccumulate.Layouts.good, BLSPrivateAccumulate.Layouts.arithmetic, BLSAccumulate.Layouts.arithmetic, BLSResponse.Layouts.points] at *; omega))
    (layout.good.fits_of_le (by have := sizes layout; have := layout.good.sizes; dsimp only [BLSPrivateAccumulate.Layouts.good, BLSPrivateAccumulate.Layouts.arithmetic, BLSAccumulate.Layouts.arithmetic, BLSResponse.Layouts.points] at *; omega)) _
theorem normalize_buffers : (normalize layout add addBuffers reserve).program.code.memBound ≤ max 2 slots + 2 :=
  (Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := max 2 slots + 1) _ _ _ _ _ _ _ _
    (evaluated_buffers layout) (saved_buffers layout add addBuffers reserve)).trans (by dsimp only [BLSPrivateAccumulate.Layouts.good, BLSPrivateAccumulate.Layouts.arithmetic, BLSAccumulate.Layouts.arithmetic, BLSResponse.Layouts.points] at *; omega)

variable [Zero F] [DecidableEq M] (zeroValid : layout.cache.value.valid 0)
def zero : layout.cache.value.Value := ⟨0, zeroValid⟩
def pairZero : layout.bad.cache.value.Value := ⟨(0, 0), zeroValid, zeroValid⟩
def admissible (value : (F × List (M × F)) × (M × (F × F))) : Prop :=
  layout.cache.admissible (value.2.1, 0, value.1.2, ())
instance (value : (F × List (M × F)) × (M × (F × F))) : Decidable (admissible layout value) :=
  inferInstanceAs (Decidable (layout.cache.admissible _))
def goodInput : Layout w ((F × List (M × F)) × (M × (F × F))) := (returned layout).restrict (admissible layout)
def prepared : Implementation .unit (goodInput layout) (CacheTargetFrame.input layout.good (zero layout zeroValid))
    (fun value => (value.1, value.2.1, value.2.2.1 + value.2.2.2)) where
  preserves value valid := ⟨(normalize layout add addBuffers reserve).preserves value valid.1, valid.2⟩
  program := ((normalize layout add addBuffers reserve).restrictInput (admissible layout)).program.viewOutput
    (CacheTargetFrame.input layout.good (zero layout zeroValid)).representation _ (fun _ => rfl)
def good : Implementation .unit (goodInput layout) layout.good.input
    (fun value => ((value.2.1, 0, value.1.2, ()), value.2.2.1 + value.2.2.2, value.1.1)) :=
  (prepared layout add addBuffers reserve zeroValid).then (CacheTargetFrame.implementation layout.good (zero layout zeroValid))
theorem good_buffers : (good layout add addBuffers reserve zeroValid).program.code.memBound ≤ max (max 2 slots + 2) 6 :=
  max_le_max (normalize_buffers layout add addBuffers reserve) (CacheTargetFrame.implementation_buffers _ _)
def badInput := CacheTargetFrame.input layout.bad (pairZero layout zeroValid)
def bad : Implementation .unit (badInput layout zeroValid) layout.bad.input
    (fun value => ((value.2.1, (0, 0), value.1.2, ()), value.2.2, value.1.1)) :=
  CacheTargetFrame.implementation layout.bad (pairZero layout zeroValid)
omit [Add F] in
theorem bad_buffers : (bad layout zeroValid).program.code.memBound ≤ 6 := CacheTargetFrame.implementation_buffers _ _
omit [Add F] in
theorem admissible_of_room (value : (returned layout).Value) (room : value.val.1.2.length ≤ layout.cache.capacityPred) :
    admissible layout value.val := fun _ => room
end Signatures.Runtime.CaliperBackend.BLSFinalFrame
