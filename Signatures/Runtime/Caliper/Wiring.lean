import Signatures.Runtime.Caliper.Slice

/-! Concrete projections of bounded layouts. The result is built in scratch
buffer 1, copied back to the local-call buffer 0, and scratch is released. These
are real local realizers, with linear code and time rather than free projections.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat}

def selectSlice (start count : Nat) : Stmt w :=
  .memAllocI 1 count ;;
  copySlice 0 1 start count ;;
  .memAllocI 0 count ;;
  copySlice 1 0 0 count ;;
  .memFree 1

theorem selectSlice_straight (start count : Nat) : (selectSlice (w := w) start count).Straight := by
  simp [selectSlice, Stmt.Straight, copySlice_straight]

theorem selectSlice_randomFree (start count : Nat) : (selectSlice (w := w) start count).RandomFree := by
  simp [selectSlice, Stmt.RandomFree, copySlice_randomFree]

theorem selectSlice_staticTime (cost : CostModel) (start count : Nat) :
    (selectSlice (w := w) start count).staticTime cost =
      2 * (cost.memAlloc + count * cost.allocPerWord) + 2 * count * sliceWordTime cost + cost.memFree := by
  simp [selectSlice, Stmt.staticTime, copySlice_staticTime]
  ring

theorem selectSlice_descriptionWords (start count : Nat) :
    descriptionWords (selectSlice (w := w) start count) = 26 * count + 14 := by
  simp only [selectSlice, descriptionWords_seq, copySlice_descriptionWords]
  simp only [descriptionWords, description, List.length_cons, List.length_nil]
  omega

theorem selectSlice_descriptionFits (start count : Nat) (hw : 16 < 2 ^ w) (hc : count < 2 ^ w) :
    DescriptionFits (selectSlice (w := w) start count) := by
  have hp := width_pos hw
  have h0 : 0 < 2 ^ w := by positivity
  have h1 : 1 < 2 ^ w := by omega
  apply DescriptionFits.seq hp (by simp [DescriptionFits, description]; omega)
  apply DescriptionFits.seq hp (copySlice_descriptionFits 0 1 start count hw h0 h1)
  apply DescriptionFits.seq hp (by simp [DescriptionFits, description]; omega)
  apply DescriptionFits.seq hp (copySlice_descriptionFits 1 0 0 count hw h1 h0)
  simp [DescriptionFits, description]; omega

theorem selectSlice_exec (cost : CostModel) (tape : RandomTape w) (start count : Nat)
    (before : State w) (span : start + count ≤ (before.bufs 0).size)
    (fits : ∀ buffer, before.caps buffer < 2 ^ w) (wellFormed : before.WellFormed) :
    ∃ after elapsed net peak,
      Caliper.Exec cost tape (selectSlice start count) before after elapsed net peak ∧
      (after.bufs 0).toList = ((before.bufs 0).toList.drop start).take count ∧
      after.regs 0 = before.regs 0 ∧ (∀ buffer, after.caps buffer < 2 ^ w) := by
  have hsource : (before.bufs 0).size < 2 ^ w := (wellFormed.size_le_cap 0).trans_lt (fits 0)
  have hcount : count < 2 ^ w := lt_of_le_of_lt (by omega) hsource
  have hlength : (((before.bufs 0).toList.drop start).take count).length = count := by
    simp only [List.length_take, List.length_drop, Array.length_toList]
    omega
  let allocated := before.allocBuf 1 count
  obtain ⟨middle, he₁, hout₁, hc₁⟩ := copySlice_exec cost tape 0 1 (by decide) count start allocated
    (by simpa [allocated] using span) (by simpa [allocated] using hsource) (by simp [allocated])
  have hm : (middle.bufs 1).toList = ((before.bufs 0).toList.drop start).take count := by
    simpa [allocated] using hout₁
  have hms : (middle.bufs 1).size = count := by
    have := congrArg List.length hm
    simpa [hlength] using this
  let reset := middle.allocBuf 0 count
  obtain ⟨last, he₂, hout₂, hc₂⟩ := copySlice_exec cost tape 1 0 (by decide) count 0 reset
    (by simp [reset, hms]) (by simpa [reset, hms] using hcount) (by simp [reset])
  let after := last.allocBuf 1 0
  have execution := Caliper.Exec.seq (Caliper.Exec.memAllocI (C := cost) (tape := tape)
      (s := before) (b := 1) (n := count))
    (Caliper.Exec.seq he₁ (Caliper.Exec.seq (Caliper.Exec.memAllocI (b := 0) (n := count))
      (Caliper.Exec.seq he₂ (Caliper.Exec.memFree (b := 1)))))
  refine ⟨after, _, _, _, execution, ?_, ?_, ?_⟩
  · simp only [after, bufs_allocBuf_ne _ _ (by decide : (0 : Nat) ≠ 1)]
    have htake : (middle.bufs 1).toList.take count = (middle.bufs 1).toList :=
      List.take_of_length_le (by simpa using le_of_eq hms)
    have hlast : (last.bufs 0).toList = (middle.bufs 1).toList := by
      simpa [reset, htake] using hout₂
    exact hlast.trans hm
  · exact execution.frame_reg (by simp [Stmt.Writes, copySlice_preserves_zero])
  · intro buffer
    change (if buffer = 1 then 0 else last.caps buffer) < 2 ^ w
    rw [hc₂]
    simp only [reset, State.allocBuf]
    rw [hc₁]
    simp only [allocated, State.allocBuf]
    split_ifs <;> first | exact hcount | exact fits buffer | positivity

variable {A B : Type}

/-- Any specified slice projection receives actual executable evidence. -/
def selectSliceRealizer (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (input : Representation w A) (output : Representation w B) (f : A → B)
    (start : Nat) (hw : 16 < 2 ^ w)
    (span : start + output.encoding.words ≤ input.encoding.words)
    (encoded : ∀ value, ((input.encoding.encode value).drop start).take output.encoding.words =
      output.encoding.encode (f value)) : Realizer cost input output f where
  code := selectSlice start output.encoding.words
  positive_width := width_pos hw
  description_fits := selectSlice_descriptionFits _ _ hw output.fits
  random_free := selectSlice_randomFree _ _
  time _ := (selectSlice (w := w) start output.encoding.words).staticTime cost
  net _ := (selectSlice (w := w) start output.encoding.words).staticTime cost
  workspace _ := (selectSlice (w := w) start output.encoding.words).staticTime cost
  correct tape value before represented := by
    have hs : (before.bufs 0).size = input.encoding.words := by
      have := congrArg List.length represented.2.1
      simpa [input.encoding.encode_length] using this
    obtain ⟨after, elapsed, net, peak, execution, hout, hr, hc⟩ :=
      selectSlice_exec cost tape start output.encoding.words before (by rwa [hs])
        represented.2.2.2 represented.2.2.1
    have ht := execution.straight_time_eq (selectSlice_straight _ _)
    subst elapsed
    refine ⟨after, net, peak, execution, ⟨hr.trans represented.1, ?_,
      execution.wellFormed_preserved represented.2.2.1, hc⟩,
      execution.net_le_time allocation, execution.peak_le_time allocation⟩
    rw [hout, represented.2.1, encoded]

def firstRealizer (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (left : Representation w A) (right : Representation w B) (hw : 16 < 2 ^ w)
    (fits : left.encoding.words + right.encoding.words < 2 ^ w) :
    Realizer cost (left.prod right fits) left Prod.fst :=
  selectSliceRealizer cost allocation (left.prod right fits) left Prod.fst 0 hw
    (by simp [Representation.prod, Encoding.prod, Encoding.checked]) (by
      intro value
      change ((left.encoding.encode value.1 ++ right.encoding.encode value.2).drop 0).take
        left.encoding.words = left.encoding.encode value.1
      rw [← left.encoding.encode_length value.1]
      simp)

def secondRealizer (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (left : Representation w A) (right : Representation w B) (hw : 16 < 2 ^ w)
    (fits : left.encoding.words + right.encoding.words < 2 ^ w) :
    Realizer cost (left.prod right fits) right Prod.snd :=
  selectSliceRealizer cost allocation (left.prod right fits) right Prod.snd left.encoding.words hw
    (by rfl) (by
      intro value
      change ((left.encoding.encode value.1 ++ right.encoding.encode value.2).drop left.encoding.words).take
        right.encoding.words = right.encoding.encode value.2
      rw [← left.encoding.encode_length value.1, ← right.encoding.encode_length value.2]
      simp)

/-- List lengths stay bounded at the machine interface. Reading the length
header uses the same proved, charged slice implementation as pair projection. -/
def listLengthRealizer (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Representation w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (count_fits : capacity < 2 ^ w)
    (storage_fits : 1 + capacity * entry.encoding.words < 2 ^ w) :
    Realizer cost (entry.boundedList capacity count_fits storage_fits)
      (Representation.fin w (capacity + 1) (width_pos hw) count_fits)
      (fun values => (⟨values.val.length, Nat.lt_succ_of_le values.property⟩ : Fin (capacity + 1))) :=
  selectSliceRealizer cost allocation _ _ _ 0 hw
    (by simp [Representation.fin, Representation.boundedList, Encoding.fin,
      Encoding.boundedList, Encoding.checked]) (by
      intro values
      simp [Representation.fin, Representation.boundedList, Encoding.fin,
        Encoding.boundedList, Encoding.checked])

end Signatures.Runtime.CaliperBackend
