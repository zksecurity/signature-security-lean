import Signatures.Runtime.Caliper.WordEquality
import Signatures.Runtime.Caliper.NameBounds
import Signatures.Runtime.Caliper.CapacityBounds
import Signatures.Runtime.Caliper.ImplementationBounds

/-! Equality from injective word encodings. The returned program scans the
stored words; decoding and source equality occur only in its correctness proof.
Bounded source layouts retain their original source types and validity domains. -/

namespace Signatures.Runtime.CaliperBackend.EncodedEquality

open Caliper WordEquality BoundedSource

variable {w : Nat} {A : Type}

def finish : Stmt w := .memAllocI 0 1 ;; .memPush 0 4
def code (words : Nat) : Stmt w := .imm 4 1 ;; scan 0 words words ;; finish

def time (cost : CostModel) (words : Nat) : Nat :=
  cost.imm + (words * wordTime cost + (cost.memAlloc + cost.allocPerWord + cost.memPush))

theorem finish_exec (cost : CostModel) (tape : RandomTape w) (before : State w) :
    ∃ after net peak, Caliper.Exec cost tape finish before after
      (cost.memAlloc + cost.allocPerWord + cost.memPush) net peak ∧
      after.bufs 0 = #[before.regs 4] ∧ after.regs 0 = before.regs 0 ∧ net ≤ 1 ∧ peak ≤ 1 := by
  let reserved := before.allocBuf 0 1
  let after := reserved.setBuf 0 #[before.regs 4]
  have allocation : Caliper.Exec cost tape (.memAllocI 0 1) before reserved
      (cost.memAlloc + cost.allocPerWord) (1 - (before.caps 0 : Int)) (max (1 - (before.caps 0 : Int)) 0) := by
    simpa using (Caliper.Exec.memAllocI (C := cost) (tape := tape) (s := before) (b := 0) (n := 1))
  have push : Caliper.Exec cost tape (.memPush 0 4) reserved after cost.memPush 0 0 := by
    convert Caliper.Exec.memPush (C := cost) (tape := tape) (s := reserved) (b := 0) (src := 4)
      (by simp [reserved]) using 1
    simp [after, reserved]
  refine ⟨after, _, _, Caliper.Exec.seq allocation push, by simp [after], rfl, ?_, ?_⟩ <;> omega

theorem code_exec (cost : CostModel) (tape : RandomTape w) (words : Nat) (before : State w)
    (span : words + words ≤ (before.bufs 0).size) (fits : (before.bufs 0).size < 2 ^ w) :
    ∃ after net peak, Caliper.Exec cost tape (code words) before after (time cost words) net peak ∧
      after.bufs 0 = #[bit (equalSlices (before.bufs 0) 0 words words)] ∧
      after.regs 0 = before.regs 0 ∧ net ≤ 1 ∧ peak ≤ 1 := by
  let initial := before.setReg 4 1
  obtain ⟨scanned, scanning, result, bytes, capacities, zero⟩ :=
    scan_exec cost tape words 0 words initial true (by simp [initial, bit])
      (by simpa [initial] using (show words ≤ (before.bufs 0).size by omega))
      (by simpa [initial] using span) (by simpa [initial] using fits)
  obtain ⟨after, net, peak, finishing, output, finalZero, netBound, peakBound⟩ := finish_exec cost tape scanned
  have peakNonneg := finishing.peak_nonneg
  have execution := Caliper.Exec.seq (Caliper.Exec.imm (C := cost) (tape := tape) (s := before) (d := 4) (v := 1))
    (Caliper.Exec.seq scanning finishing)
  refine ⟨after, net, peak, ?_, ?_, finalZero.trans zero, netBound, peakBound⟩
  · simpa [code, time, max_eq_right peakNonneg] using execution
  · simpa [initial] using output.trans (congrArg (fun value => #[value]) result)

theorem code_descriptionFits (words : Nat) (hw : 16 < 2 ^ w) : DescriptionFits (code (w := w) words) := by
  have positive := (width_pos hw).ne'
  apply DescriptionFits.seq (width_pos hw)
  · simp [DescriptionFits, description]
    omega
  · apply DescriptionFits.seq (width_pos hw) (scan_descriptionFits _ _ _ hw)
    simp [finish, DescriptionFits, description, positive]
    omega

theorem code_randomFree (words : Nat) : (code (w := w) words).RandomFree :=
  ⟨trivial, scan_randomFree _ _ _, trivial, trivial⟩

theorem code_descriptionWords (words : Nat) : descriptionWords (code (w := w) words) = 30 * words + 13 := by
  simp only [code, descriptionWords_seq, scan_descriptionWords]
  have immWords : descriptionWords (.imm 4 1 : Stmt w) = 3 := rfl
  have finishWords : descriptionWords (finish : Stmt w) = 7 := rfl
  rw [immWords, finishWords]
  omega

theorem code_names (words : Nat) : NamesBound (code (w := w) words) 5 := by
  have scanned : ∀ count left right, NamesBound (scan (w := w) left right count) 5 := by
    intro count
    induction count with
    | zero => intro left right; exact ⟨by simp [scan, registerSlots], by simp [scan, Stmt.memBound]⟩
    | succ count ih =>
      intro left right
      have bounded := ih (left + 1) (right + 1)
      constructor <;> simp only [scan, step, registerSlots, Stmt.memBound] <;>
        have registers := bounded.registers <;> have buffers := bounded.buffers <;> omega
  have bounded := scanned words 0 words
  constructor <;> simp only [code, finish, registerSlots, Stmt.memBound] <;>
    have registers := bounded.registers <;> have buffers := bounded.buffers <;> omega

theorem time_unit (words : Nat) : time .unit words = 6 * words + 3 := by
  dsimp [time, wordTime, CostModel.unit]
  omega

theorem equalSlices_encoding [DecidableEq A] (representation : Representation w A)
    (left right : A) (bytes : Array (Word w))
    (contents : bytes.toList = representation.encoding.encode left ++ representation.encoding.encode right) :
    equalSlices bytes 0 representation.encoding.words representation.encoding.words = decide (left = right) := by
  have size := congrArg List.length contents
  simp only [Array.length_toList, List.length_append, representation.encoding.encode_length] at size
  rw [equalSlices_eq _ _ _ _ (by omega) (by omega), contents]
  have leftLength := representation.encoding.encode_length left
  have rightLength := representation.encoding.encode_length right
  simp only [List.drop_zero]
  rw [← leftLength, List.take_left, List.drop_left]
  rw [leftLength, ← rightLength, List.take_length]
  exact decide_eq_decide.mpr representation.encoding.encode_injective.eq_iff

def realizer [DecidableEq A] (cost : CostModel) (representation : Representation w A) (hw : 16 < 2 ^ w)
    (fits : representation.encoding.words + representation.encoding.words < 2 ^ w) :
    Realizer cost (representation.prod representation fits) (Representation.boolean w (width_pos hw))
      (fun value => decide (value.1 = value.2)) where
  code := code representation.encoding.words
  positive_width := width_pos hw
  description_fits := code_descriptionFits _ hw
  random_free := code_randomFree _
  time _ := time cost representation.encoding.words
  net _ := 1
  workspace _ := 1
  correct tape value before represented := by
    have contents : (before.bufs 0).toList = representation.encoding.encode value.1 ++ representation.encoding.encode value.2 := represented.2.1
    have size := congrArg List.length contents
    simp only [Array.length_toList, List.length_append, representation.encoding.encode_length] at size
    obtain ⟨after, net, peak, execution, output, zero, netBound, peakBound⟩ :=
      code_exec cost tape representation.encoding.words before size.ge (by rw [size]; exact fits)
    refine ⟨after, net, peak, execution, ⟨zero.trans represented.1, ?_,
      execution.wellFormed_preserved represented.2.2.1,
      capacities_preserved execution (code_descriptionFits _ hw).allocationsFit represented.2.2.2⟩, netBound, peakBound⟩
    rw [output, equalSlices_encoding representation value.1 value.2 _ contents]
    rfl

def implementation [DecidableEq A] (cost : CostModel) (layout : Layout w A) (hw : 16 < 2 ^ w)
    (fits : layout.representation.encoding.words + layout.representation.encoding.words < 2 ^ w) :
    Implementation cost (layout.prod layout fits) (DataImplementation.boolLayout w (width_pos hw))
      (fun value => decide (value.1 = value.2)) where
  preserves _ _ := trivial
  program := ((realizer cost layout.representation hw fits).viewInput _ (productView layout layout)
    (fun _ => rfl)).viewOutput _ _ (by
      intro value
      change [bit (decide (value.val.1 = value.val.2))] =
        [bit (decide ((⟨value.val.1, value.property.1⟩ : layout.Value) = ⟨value.val.2, value.property.2⟩))]
      simp only [Subtype.mk.injEq])

theorem implementation_boundedBy [DecidableEq A] (layout : Layout w A) (hw : 16 < 2 ^ w)
    (fits : layout.representation.encoding.words + layout.representation.encoding.words < 2 ^ w) :
    (implementation .unit layout hw fits).BoundedBy (6 * layout.representation.encoding.words + 3)
      (30 * layout.representation.encoding.words + 13) :=
  ⟨fun _ => (time_unit _).le, (code_descriptionWords _).le⟩

theorem implementation_names [DecidableEq A] (cost : CostModel) (layout : Layout w A) (hw : 16 < 2 ^ w)
    (fits : layout.representation.encoding.words + layout.representation.encoding.words < 2 ^ w) :
    NamesBound (implementation cost layout hw fits).program.code 5 := code_names _

end Signatures.Runtime.CaliperBackend.EncodedEquality
