import Proofs.Runtime.Caliper.SchnorrROMTapeTrimStep

/-! Resource bounds for the actual replay scan body. All comparisons, list
padding, stored branches and copies are included. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F) (i : Fin layout.capacity)

theorem current_bounded : (current layout i).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals
    have size := layout.state_le i.val (by omega)
    change (layout.states i.castSucc).representation.encoding.words ≤ layout.width at size
    have tailSize : (layout.stateTail i.castSucc).representation.encoding.words =
        (layout.states i.castSucc).representation.encoding.words := by change _ + 0 = _; omega
    dsimp only [Layouts.stateTail] at tailSize
    rw [tailSize]
    omega
theorem entry_bounded : (entry layout i).BoundedBy (8 * layout.width) (26 * layout.width + 14) :=
  (Implementation.first_boundedBy _ _ _ _).mono
    (Nat.mul_le_mul_left _ layout.entry_le) (by have := layout.entry_le; omega)
theorem tag_bounded : (tag layout i).BoundedBy (8 * layout.width + 8) (26 * layout.width + 55) := by
  apply ((entry_bounded layout i).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals rw [Layouts.counter_words]
theorem remaining_bounded : (remaining layout i).BoundedBy (16 * layout.width + 8) (52 * layout.width + 70) := by
  apply ((current_bounded layout i).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals rw [Layouts.counter_words]
theorem accumulated_bounded : (accumulated layout i).BoundedBy (24 * layout.width) (78 * layout.width + 44) := by
  apply ((current_bounded layout i).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals simp only [Fin.val_castSucc]; have := layout.list_le i.val (by omega); omega
theorem constant_bounded (n : Nat) (valid : n < 2 ^ w) :
    (constant layout i n valid).BoundedBy 8 40 := Implementation.constant_bounded _ _ _ _

theorem arguments_bounded {f : Schnorr.TapeCell F × ((Nat × List (Schnorr.TapeCell F)) × Unit) → Nat}
    (get : Implementation .unit (layout.body i) layout.counter f)
    (getBuffers : get.program.code.memBound ≤ 2) (n : Nat) (valid : n < 2 ^ w)
    {time words : Nat} (bound : get.BoundedBy time words) :
    (arguments layout i get getBuffers n valid).BoundedBy
      (time + 104 * layout.width + 60) (words + 338 * layout.width + 333) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ bound (constant_bounded layout i n valid)).mono
  all_goals rw [Layouts.counter_words]; have := layout.body_le i; omega

theorem isChallenge_bounded : (isChallenge layout i).BoundedBy (200 * layout.width + 100) (700 * layout.width + 600) := by
  have primitive : (Natural.equal .unit (2 ^ w) (2 ^ w) layout.wordFits le_rfl le_rfl).BoundedBy 6 27 :=
    ⟨fun _ => le_rfl, (WordBinary.descriptionWords_eq .eq).le⟩
  exact ((arguments_bounded layout i _ _ _ _ (tag_bounded layout i)).then primitive).mono (by omega) (by omega)
theorem isZero_bounded : (isZero layout i).BoundedBy (200 * layout.width + 100) (700 * layout.width + 600) := by
  have primitive : (Natural.equal .unit (2 ^ w) (2 ^ w) layout.wordFits le_rfl le_rfl).BoundedBy 6 27 :=
    ⟨fun _ => le_rfl, (WordBinary.descriptionWords_eq .eq).le⟩
  exact ((arguments_bounded layout i _ _ _ _ (remaining_bounded layout i)).then primitive).mono (by omega) (by omega)
theorem decrement_bounded : (decrement layout i).BoundedBy (200 * layout.width + 100) (700 * layout.width + 600) := by
  have primitive : (Natural.subtract .unit (2 ^ w) (2 ^ w) layout.wordFits le_rfl le_rfl).BoundedBy 8 38 :=
    ⟨fun value => (Natural.subtract_time_unit _ _ _ _ _ value).le, Saturating.descriptionWords_eq.le⟩
  exact ((arguments_bounded layout i _ _ _ _ (remaining_bounded layout i)).then primitive).mono (by omega) (by omega)

theorem consArgs_bounded : (consArgs layout i).BoundedBy (188 * layout.width) (611 * layout.width + 182) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (entry_bounded layout i) (accumulated_bounded layout i)).mono
  all_goals have := layout.body_le i; have := layout.entry_le; have := layout.list_le i.val (by omega); omega
theorem cons_bounded : (cons layout i).BoundedBy (200 * layout.width + 20) (700 * layout.width + 250) := by
  apply ((consArgs_bounded layout i).then (ListData.cons_boundedBy _ _ _ _ _)).mono
  all_goals
    have size := layout.list_le (i.val + 1) (by omega)
    rw [Layouts.list_words] at size
    omega
theorem widen_bounded : (widen layout i).BoundedBy (32 * layout.width) (104 * layout.width + 59) := by
  apply ((accumulated_bounded layout i).then (ListData.widen_boundedBy _ _ _ _ _ _ _)).mono
  all_goals
    have size := layout.list_le (i.val + 1) (by omega)
    rw [Layouts.list_words] at size
    omega
theorem assemble_bounded {f : Schnorr.TapeCell F × ((Nat × List (Schnorr.TapeCell F)) × Unit) → Nat}
    {g : Schnorr.TapeCell F × ((Nat × List (Schnorr.TapeCell F)) × Unit) → List (Schnorr.TapeCell F)}
    (count : Implementation .unit (layout.body i) layout.counter f)
    (values : Implementation .unit (layout.body i) (layout.list (i.val + 1) (by omega)) g)
    (countBuffers : count.program.code.memBound ≤ 3) (valuesBuffers : values.program.code.memBound ≤ 3)
    {countTime countWords valuesTime valuesWords : Nat}
    (countBound : count.BoundedBy countTime countWords) (valuesBound : values.BoundedBy valuesTime valuesWords) :
    (assemble layout i count values countBuffers valuesBuffers).BoundedBy
      (countTime + valuesTime + 120 * layout.width + 36) (countWords + valuesWords + 390 * layout.width + 241) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ countBound valuesBound).mono
  all_goals rw [Layouts.counter_words]; have := layout.body_le i; have := layout.list_le (i.val + 1) (by omega); omega

theorem skip_bounded : (skip layout i).BoundedBy (600 * layout.width + 200) (2000 * layout.width + 1200) :=
  (assemble_bounded layout i _ _ _ _ (remaining_bounded layout i) (widen_bounded layout i)).mono (by omega) (by omega)
theorem keep_bounded : (keep layout i).BoundedBy (600 * layout.width + 200) (2000 * layout.width + 1200) :=
  (assemble_bounded layout i _ _ _ _ (remaining_bounded layout i) (cons_bounded layout i)).mono (by omega) (by omega)
theorem consume_bounded : (consume layout i).BoundedBy (600 * layout.width + 200) (2000 * layout.width + 1200) :=
  (assemble_bounded layout i _ _ _ _ (decrement_bounded layout i) (cons_bounded layout i)).mono (by omega) (by omega)
theorem challenge_bounded : (challenge layout i).BoundedBy (1600 * layout.width + 600) (6000 * layout.width + 3500) := by
  apply (Implementation.checkedBranch_boundedBy _ _ _ (layout.bodyDuplicate i) (layout.bodyTag i) _ _ _ _ _ _
    (isZero_bounded layout i) (skip_bounded layout i) (consume_bounded layout i) (challenge layout i)
    (Option.eq_some_of_isSome (challenge_accepted layout i))).mono
  all_goals have := layout.body_le i; omega
theorem body_bounded : (body layout i).BoundedBy (2700 * layout.width + 1000) (10000 * layout.width + 6000) := by
  have bound := Implementation.checkedBranch_boundedBy _ _ _ (layout.bodyDuplicate i) (layout.bodyTag i) _ _ _ _ _ _
    (isChallenge_bounded layout i) (challenge_bounded layout i) (keep_bounded layout i)
    ((bodyCompiled layout i).get (body_accepted layout i)) (Option.eq_some_of_isSome (body_accepted layout i))
  constructor
  · intro value; exact (bound.time_le value).trans (by have := layout.body_le i; omega)
  · exact bound.code_le.trans (by have := layout.body_le i; omega)

variable (slots : Nat)
theorem current_names : NamesAccounted (current layout i).program.code slots :=
  (Implementation.second_names _ _ _ _ slots).seq (Implementation.first_names _ _ _ _ slots)
theorem entry_names : NamesAccounted (entry layout i).program.code slots := Implementation.first_names _ _ _ _ slots
theorem tag_names : NamesAccounted (tag layout i).program.code slots :=
  (entry_names layout i slots).seq (Implementation.first_names _ _ _ _ slots)
theorem remaining_names : NamesAccounted (remaining layout i).program.code slots :=
  (current_names layout i slots).seq (Implementation.first_names _ _ _ _ slots)
theorem accumulated_names : NamesAccounted (accumulated layout i).program.code slots :=
  (current_names layout i slots).seq (Implementation.second_names _ _ _ _ slots)
theorem arguments_names {f : Schnorr.TapeCell F × ((Nat × List (Schnorr.TapeCell F)) × Unit) → Nat}
    (get : Implementation .unit (layout.body i) layout.counter f)
    (getBuffers : get.program.code.memBound ≤ 2) (n : Nat) (valid : n < 2 ^ w)
    (bound : NamesAccounted get.program.code slots) :
    NamesAccounted (arguments layout i get getBuffers n valid).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ bound (Implementation.constant_names _ _ _ _ slots)
theorem isChallenge_names : NamesAccounted (isChallenge layout i).program.code slots := by
  apply (arguments_names layout i slots _ _ _ _ (tag_names layout i slots)).seq
  exact ⟨by change 3 ≤ slots + 27; omega, by change 1 ≤ slots + 27; omega⟩
theorem isZero_names : NamesAccounted (isZero layout i).program.code slots := by
  apply (arguments_names layout i slots _ _ _ _ (remaining_names layout i slots)).seq
  exact ⟨by change 3 ≤ slots + 27; omega, by change 1 ≤ slots + 27; omega⟩
theorem decrement_names : NamesAccounted (decrement layout i).program.code slots := by
  apply (arguments_names layout i slots _ _ _ _ (remaining_names layout i slots)).seq
  exact ⟨by change 4 ≤ slots + 38; omega, by change 1 ≤ slots + 38; omega⟩
theorem cons_names : NamesAccounted (cons layout i).program.code slots :=
  (Implementation.pair_names _ _ _ _ _ _ _ _ (entry_names layout i slots) (accumulated_names layout i slots)).seq
    (ListData.cons_names _ _ _ _ _ slots)
theorem widen_names : NamesAccounted (widen layout i).program.code slots :=
  (accumulated_names layout i slots).seq (ListData.widen_names _ _ _ _ _ _ _ slots)
theorem assemble_names {f : Schnorr.TapeCell F × ((Nat × List (Schnorr.TapeCell F)) × Unit) → Nat}
    {g : Schnorr.TapeCell F × ((Nat × List (Schnorr.TapeCell F)) × Unit) → List (Schnorr.TapeCell F)}
    (count : Implementation .unit (layout.body i) layout.counter f)
    (values : Implementation .unit (layout.body i) (layout.list (i.val + 1) (by omega)) g)
    (countBuffers : count.program.code.memBound ≤ 3) (valuesBuffers : values.program.code.memBound ≤ 3)
    (countNames : NamesAccounted count.program.code slots) (valuesNames : NamesAccounted values.program.code slots) :
    NamesAccounted (assemble layout i count values countBuffers valuesBuffers).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ countNames valuesNames
theorem skip_names : NamesAccounted (skip layout i).program.code slots :=
  assemble_names layout i slots _ _ _ _ (remaining_names layout i slots) (widen_names layout i slots)
theorem keep_names : NamesAccounted (keep layout i).program.code slots :=
  assemble_names layout i slots _ _ _ _ (remaining_names layout i slots) (cons_names layout i slots)
theorem consume_names : NamesAccounted (consume layout i).program.code slots :=
  assemble_names layout i slots _ _ _ _ (decrement_names layout i slots) (cons_names layout i slots)
theorem challenge_names : NamesAccounted (challenge layout i).program.code slots :=
  Implementation.checkedBranch_names _ _ _ (layout.bodyDuplicate i) (layout.bodyTag i)
    (isZero_names layout i slots) (skip_names layout i slots) (consume_names layout i slots) (challenge layout i)
    (Option.eq_some_of_isSome (challenge_accepted layout i))
theorem body_names : NamesAccounted (body layout i).program.code slots :=
  Implementation.checkedBranch_names _ _ _ (layout.bodyDuplicate i) (layout.bodyTag i)
    (isChallenge_names layout i slots) (challenge_names layout i slots) (keep_names layout i slots)
    ((bodyCompiled layout i).get (body_accepted layout i)) (Option.eq_some_of_isSome (body_accepted layout i))

end Signatures.Runtime.CaliperBackend.SchnorrROMTape
