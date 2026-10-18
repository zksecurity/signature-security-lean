import Signatures.Runtime.Caliper.Construct

/-! Executable dispatch on encoded tagged unions. The branch reads the stored
tag, normalizes the chosen payload by charged copying, and executes the selected
callee. Its specification applies to represented (canonical) inputs.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat} {A B D : Type}

namespace Dispatch

def code (left right : Stmt w) (leftWords rightWords : Nat) : Stmt w :=
  .memLoad 1 0 0 ;;
  .ifNZ 1 (selectSlice 1 rightWords ;; right) (selectSlice 1 leftWords ;; left)

theorem code_descriptionWords (left right : Stmt w) (leftWords rightWords : Nat) :
    descriptionWords (code left right leftWords rightWords) =
      descriptionWords left + descriptionWords right + 26 * leftWords + 26 * rightWords + 37 := by
  have hi (condition : Reg) (yes no : Stmt w) :
      descriptionWords (.ifNZ condition yes no) = descriptionWords yes + descriptionWords no + 2 := by
    simp [descriptionWords, description]
  simp only [code, descriptionWords_seq, hi, selectSlice_descriptionWords]
  simp only [descriptionWords, description, List.length_cons, List.length_nil]
  omega

theorem load_tag (cost : CostModel) (tape : RandomTape w) (tag : Word w)
    (rest : List (Word w)) (before : State w) (zero : before.regs 0 = 0)
    (contents : (before.bufs 0).toList = tag :: rest) :
    Caliper.Exec cost tape (.memLoad 1 0 0) before (before.setReg 1 tag) cost.memLoad 0 0 := by
  have hlength := congrArg List.length contents
  have hs : 0 < (before.bufs 0).size := by simp only [Array.length_toList, List.length_cons] at hlength; omega
  have hv : (before.bufs 0)[0] = tag := by
    have h : (before.bufs 0).toList[0]? = some tag := by rw [contents]; rfl
    simpa [hs] using h
  convert Caliper.Exec.memLoad (C := cost) (tape := tape) (s := before) (d := 1)
    (b := 0) (i := 0) (by simpa [zero] using hs) using 1
  simp [zero, hv]

theorem payload_exec {cost : CostModel} {input : Representation w A} {output : Representation w D}
    {f : A → D} (body : Realizer cost input output f) (tape : RandomTape w)
    (value : A) (tag : Word w) (padding : List (Word w)) (before : State w)
    (zero : before.regs 0 = 0) (contents : (before.bufs 0).toList = tag :: (input.encoding.encode value ++ padding))
    (wellFormed : before.WellFormed) (capacities : ∀ b, before.caps b < 2 ^ w) :
    ∃ after net peak,
      Caliper.Exec cost tape (selectSlice 1 input.encoding.words ;; body.code) before after
        ((selectSlice (w := w) 1 input.encoding.words).staticTime cost + body.time value) net peak ∧
      output.Holds (f value) after := by
  have hlength := congrArg List.length contents
  have span : 1 + input.encoding.words ≤ (before.bufs 0).size := by
    simp only [Array.length_toList, List.length_cons, List.length_append, input.encoding.encode_length] at hlength
    omega
  obtain ⟨middle, elapsed, net, peak, execution, payload, offset, caps⟩ :=
    selectSlice_exec cost tape 1 input.encoding.words before span capacities wellFormed
  have ht := execution.straight_time_eq (selectSlice_straight _ _)
  subst elapsed
  have represented : input.Holds value middle := by
    refine ⟨offset.trans zero, ?_, execution.wellFormed_preserved wellFormed, caps⟩
    rw [payload, contents, ← input.encoding.encode_length value]
    simp
  obtain ⟨after, d, p, called, result, _, _⟩ := body.correct tape value middle represented
  exact ⟨after, _, _, Caliper.Exec.seq execution called, result⟩

def time (cost : CostModel) (leftWords rightWords : Nat) (leftTime : A → Nat) (rightTime : B → Nat) :
    A ⊕ B → Nat
  | .inl value => cost.memLoad + (cost.branch + ((selectSlice (w := w) 1 leftWords).staticTime cost + leftTime value))
  | .inr value => cost.memLoad + (cost.branch + ((selectSlice (w := w) 1 rightWords).staticTime cost + rightTime value))

end Dispatch

def branchRealizer (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (left : Representation w A) (right : Representation w B) (output : Representation w D)
    {f : A → D} {g : B → D} (leftBody : Realizer cost left output f) (rightBody : Realizer cost right output g)
    (hw : 16 < 2 ^ w) (fits : 1 + max left.encoding.words right.encoding.words < 2 ^ w) :
    Realizer cost (left.sum right (width_pos hw) fits) output (Sum.elim f g) where
  code := Dispatch.code leftBody.code rightBody.code left.encoding.words right.encoding.words
  positive_width := width_pos hw
  description_fits := by
    apply DescriptionFits.seq (width_pos hw) (by simp [DescriptionFits, description, (width_pos hw).ne']; omega)
    have hl := DescriptionFits.seq (width_pos hw) (selectSlice_descriptionFits 1 _ hw left.fits) leftBody.description_fits
    have hr := DescriptionFits.seq (width_pos hw) (selectSlice_descriptionFits 1 _ hw right.fits) rightBody.description_fits
    intro token member
    simp only [description, List.mem_cons, List.mem_append] at member
    rcases member with rfl | rfl | member | member
    · omega
    · exact Nat.one_lt_two_pow (width_pos hw).ne'
    · apply hr token
      simpa only [description, List.mem_cons, List.mem_append] using member
    · apply hl token
      simpa only [description, List.mem_cons, List.mem_append] using member
  random_free := by simp [Dispatch.code, Stmt.RandomFree, selectSlice_randomFree,
    leftBody.random_free, rightBody.random_free]
  time := Dispatch.time (w := w) cost left.encoding.words right.encoding.words leftBody.time rightBody.time
  net value := Dispatch.time (w := w) cost left.encoding.words right.encoding.words leftBody.time rightBody.time value
  workspace value := Dispatch.time (w := w) cost left.encoding.words right.encoding.words leftBody.time rightBody.time value
  correct tape value before represented := by
    cases value with
    | inl value =>
      have contents : (before.bufs 0).toList = (0 : Word w) :: (left.encoding.encode value ++
          List.replicate (max left.encoding.words right.encoding.words - left.encoding.words) 0) := represented.2.1
      have loaded := Dispatch.load_tag cost tape 0 _ before represented.1 contents
      obtain ⟨after, net, peak, called, result⟩ := Dispatch.payload_exec leftBody tape value 0 _
        (before.setReg 1 0) (by simpa using represented.1) contents
        (loaded.wellFormed_preserved represented.2.2.1) represented.2.2.2
      have execution := Caliper.Exec.seq loaded (Caliper.Exec.ifNZ_false (c := 1)
        (thn := selectSlice 1 right.encoding.words ;; rightBody.code) (by simp) called)
      exact ⟨after, _, _, execution, result, execution.net_le_time allocation, execution.peak_le_time allocation⟩
    | inr value =>
      have contents : (before.bufs 0).toList = (1 : Word w) :: (right.encoding.encode value ++
          List.replicate (max left.encoding.words right.encoding.words - right.encoding.words) 0) := represented.2.1
      have loaded := Dispatch.load_tag cost tape 1 _ before represented.1 contents
      obtain ⟨after, net, peak, called, result⟩ := Dispatch.payload_exec rightBody tape value 1 _
        (before.setReg 1 1) (by simpa using represented.1) contents
        (loaded.wellFormed_preserved represented.2.2.1) represented.2.2.2
      have execution := Caliper.Exec.seq loaded (Caliper.Exec.ifNZ_true (c := 1)
        (els := selectSlice 1 left.encoding.words ;; leftBody.code) (by simp [(width_pos hw).ne']) called)
      exact ⟨after, _, _, execution, result, execution.net_le_time allocation, execution.peak_le_time allocation⟩

end Signatures.Runtime.CaliperBackend
