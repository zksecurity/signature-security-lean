import Proofs.Runtime.Caliper.AttachStep

/-! Derived budgets and generated-name bounds for an attachment step, including
the complete coefficient scan and all retained input and row copies. -/

namespace Signatures.Runtime.CaliperBackend.AttachRows
open Caliper BoundedSource
variable {w : Nat} {K V : Type} (layout : Layouts w K V)

def indexWidth : Nat := 3 + (layout.coefficients + 1) * layout.value.representation.encoding.words
def indexTime : Nat := 384 * indexWidth layout + 88 + layout.coefficients * (1088 * indexWidth layout + 407)
def indexCode : Nat := 1248 * indexWidth layout + 927 + layout.coefficients * (3638 * indexWidth layout + 2615)
def bodyTime : Nat := 1100 * layout.width + 200 + indexTime layout
def bodyCode : Nat := 3600 * layout.width + 1500 + indexCode layout

variable (i : Fin layout.capacity)

theorem key_bounded : (key layout i).BoundedBy (32 * layout.width + 8) (104 * layout.width + 70) := by
  apply (Implementation.first_boundedBy _ _ _ _).mono
  all_goals have := layout.base_sizes; omega
theorem current_bounded : (current layout i).BoundedBy (24 * layout.width) (78 * layout.width + 29) := by
  apply ((Implementation.second_boundedBy layout.key (layout.context i) layout.wordFits _).then
    (Implementation.first_boundedBy (layout.states i.castSucc) layout.env layout.wordFits _)).mono
  all_goals have := layout.context_size i; have := layout.stage_sizes i.castSucc; omega
theorem counter_bounded : (counter layout i).BoundedBy (32 * layout.width + 8) (104 * layout.width + 70) := by
  apply ((current_bounded layout i).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals simp only [Layouts.counter_words]; omega
theorem previous_bounded : (previous layout i).BoundedBy (32 * layout.width + 8) (104 * layout.width + 70) := by
  apply ((current_bounded layout i).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals have := layout.stage_sizes i.castSucc; omega
theorem environment_bounded : (environment layout i).BoundedBy (32 * layout.width + 8) (104 * layout.width + 70) := by
  apply ((Implementation.second_boundedBy layout.key (layout.context i) layout.wordFits _).then
    (Implementation.second_boundedBy (layout.states i.castSucc) layout.env layout.wordFits _)).mono
  all_goals have := layout.context_size i; have := layout.base_sizes; omega
theorem lookupInput_bounded : (lookupInput layout i).BoundedBy (236 * layout.width + 52) (767 * layout.width + 381) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (counter_bounded layout i) (environment_bounded layout i)).mono
  all_goals simp only [Layouts.counter_words]; have := layout.body_size i; have := layout.base_sizes; omega
theorem coefficient_bounded : (coefficient layout i).BoundedBy
    (236 * layout.width + 52 + indexTime layout) (767 * layout.width + 382 + indexCode layout) := by
  have scan : (ListIndex.implementation (layout.indexing i)).BoundedBy (indexTime layout) (indexCode layout) := ListIndex.bounded _
  exact ((lookupInput_bounded layout i).then scan).mono (by omega) (by omega)
theorem row_bounded : (row layout i).BoundedBy
    (476 * layout.width + 60 + indexTime layout) (1547 * layout.width + 576 + indexCode layout) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (key_bounded layout i) (coefficient_bounded layout i)).mono
  all_goals
    have same : (layout.indexing i).value.representation.encoding.words = layout.value.representation.encoding.words := rfl
    have := layout.body_size i; have := layout.base_sizes; omega
theorem consArgs_bounded : (consArgs layout i).BoundedBy
    (716 * layout.width + 68 + indexTime layout) (2327 * layout.width + 770 + indexCode layout) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (row_bounded layout i) (previous_bounded layout i)).mono
  all_goals have := layout.body_size i; have := layout.base_sizes; have := layout.stage_sizes i.castSucc; omega
theorem updated_bounded : (updated layout i).BoundedBy
    (724 * layout.width + 73 + indexTime layout) (2353 * layout.width + 809 + indexCode layout) := by
  have consBound := ListData.cons_boundedBy layout.row i.val layout.wordFits
    (show i.val + 1 < 2 ^ w by have := layout.countFits; omega) (layout.rows i.succ).representation.fits
  apply ((consArgs_bounded layout i).then consBound).mono
  all_goals have size := (layout.stage_sizes i.succ).1; change 1 + (i.val + 1) * _ ≤ layout.width at size; omega
theorem one_bounded : (one layout i).BoundedBy 8 40 := Implementation.constant_bounded _ _ _ _
theorem addArgs_bounded : (addArgs layout i).BoundedBy (188 * layout.width + 68) (611 * layout.width + 403) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (counter_bounded layout i) (one_bounded layout i)).mono
  all_goals
    have size : (oneLayout layout).representation.encoding.words = 1 := rfl
    simp only [Layouts.counter_words, size]
    have := layout.body_size i
    omega
theorem advance_bounded : (advance layout i).BoundedBy (188 * layout.width + 74) (611 * layout.width + 431) := by
  have primitive : (Natural.add .unit (i.val + 1) 2 layout.wordFits (by have := layout.counterFits; omega)).BoundedBy 6 27 :=
    ⟨fun value => (Natural.add_time_unit _ _ _ _ value).le, (WordBinary.descriptionWords_eq .add).le⟩
  have combined := (addArgs_bounded layout i).then primitive
  exact ⟨fun value => (combined.time_le value).trans (by omega), combined.code_le.trans (by omega)⟩
theorem body_bounded : (body layout i).BoundedBy (bodyTime layout) (bodyCode layout) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (advance_bounded layout i) (updated_bounded layout i)).mono
  all_goals
    simp only [Layouts.counter_words]
    have := layout.body_size i
    have := layout.stage_sizes i.succ
    dsimp only [bodyTime, bodyCode]
    omega

theorem key_names (slots : Nat) : NamesAccounted (key layout i).program.code slots := Implementation.first_names _ _ _ _ slots
theorem current_names (slots : Nat) : NamesAccounted (current layout i).program.code slots :=
  (Implementation.second_names _ _ _ _ slots).seq (Implementation.first_names _ _ _ _ slots)
theorem counter_names (slots : Nat) : NamesAccounted (counter layout i).program.code slots :=
  (current_names layout i slots).seq (Implementation.first_names _ _ _ _ slots)
theorem previous_names (slots : Nat) : NamesAccounted (previous layout i).program.code slots :=
  (current_names layout i slots).seq (Implementation.second_names _ _ _ _ slots)
theorem environment_names (slots : Nat) : NamesAccounted (environment layout i).program.code slots :=
  (Implementation.second_names _ _ _ _ slots).seq (Implementation.second_names _ _ _ _ slots)
theorem lookupInput_names (slots : Nat) : NamesAccounted (lookupInput layout i).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (counter_names layout i slots) (environment_names layout i slots)
theorem coefficient_names (slots : Nat) : NamesAccounted (coefficient layout i).program.code slots :=
  (lookupInput_names layout i slots).seq (ListIndex.names _ slots)
theorem row_names (slots : Nat) : NamesAccounted (row layout i).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (key_names layout i slots) (coefficient_names layout i slots)
theorem consArgs_names (slots : Nat) : NamesAccounted (consArgs layout i).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (row_names layout i slots) (previous_names layout i slots)
theorem updated_names (slots : Nat) : NamesAccounted (updated layout i).program.code slots :=
  (consArgs_names layout i slots).seq (ListData.cons_names _ _ _ _ _ slots)
theorem one_names (slots : Nat) : NamesAccounted (one layout i).program.code slots := Implementation.constant_names _ _ _ _ slots
theorem addArgs_names (slots : Nat) : NamesAccounted (addArgs layout i).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (counter_names layout i slots) (one_names layout i slots)
theorem advance_names (slots : Nat) : NamesAccounted (advance layout i).program.code slots := by
  apply (addArgs_names layout i slots).seq
  constructor
  · change 3 ≤ slots + 27; omega
  · change 1 ≤ slots + 27; omega
theorem body_names (slots : Nat) : NamesAccounted (body layout i).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (advance_names layout i slots) (updated_names layout i slots)

end Signatures.Runtime.CaliperBackend.AttachRows
