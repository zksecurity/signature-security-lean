import Signatures.Runtime.Caliper.ListFold

/-! Uniform code and execution bounds for the compiled list fold. These include
the stored branches, copied tail/environment, body calls and frame rebuilding. -/

namespace Signatures.Runtime.CaliperBackend.ListFold

open Caliper Assembly

variable {w : Nat} {A B E : Type}

theorem code_randomFree (body : Stmt w) (free : body.RandomFree) (buffer entry state env capacity : Nat) :
    (code body buffer entry state env capacity).RandomFree := by
  induction capacity with
  | zero => exact selectSlice_randomFree _ _
  | succ capacity ih =>
    simpa [code, Stmt.RandomFree, prepare_randomFree, Retain.code, Retain.save_randomFree,
      selectSlice_randomFree, Assembly.code_randomFree, free] using ih

variable (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Representation w A) (state : Representation w B) (env : Representation w E)
    (argFits : entry.encoding.words + state.encoding.words + env.encoding.words < 2 ^ w)
    (hw : 16 < 2 ^ w) {f : A × (B × E) → B}
    (body : Realizer cost (argument entry state env argFits) state f)
    (nameFits : body.savedBuffer < 2 ^ w)

include allocation hw nameFits in
theorem code_descriptionFits (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.encoding.words + state.encoding.words + 2 * env.encoding.words < 2 ^ w) :
    DescriptionFits (code body.code body.savedBuffer entry.encoding.words state.encoding.words env.encoding.words capacity) := by
  induction capacity with
  | zero => exact selectSlice_descriptionFits _ _ hw state.fits
  | succ capacity ih =>
    have smallerCount : capacity < 2 ^ w := by omega
    have smallerStorage : 1 + capacity * entry.encoding.words + state.encoding.words + 2 * env.encoding.words < 2 ^ w := by nlinarith
    let savedRep := saved entry env capacity smallerCount (by nlinarith)
    have retained : DescriptionFits (Retain.code body.code body.savedBuffer
        (entry.encoding.words + (state.encoding.words + env.encoding.words)) state.encoding.words
        (1 + capacity * entry.encoding.words + env.encoding.words)) :=
      (body.retain allocation savedRep hw nameFits (by
        change (entry.encoding.words + (state.encoding.words + env.encoding.words)) +
          (1 + capacity * entry.encoding.words + env.encoding.words) < 2 ^ w
        nlinarith) (by
        change state.encoding.words + (1 + capacity * entry.encoding.words + env.encoding.words) < 2 ^ w
        nlinarith)).description_fits
    have rearranged := Assembly.code_descriptionFits
      (Reorder.operands (w := w) state.encoding.words (1 + capacity * entry.encoding.words) env.encoding.words) hw
      (by rw [Reorder.operands_length]; nlinarith) (Reorder.operands_names _ _ _)
    have continued := DescriptionFits.seq (width_pos hw)
      (prepare_descriptionFits _ _ _ _ hw storageFits)
      (DescriptionFits.seq (width_pos hw) retained
        (DescriptionFits.seq (width_pos hw) rearranged (ih smallerCount smallerStorage)))
    have stopped := selectSlice_descriptionFits (w := w) (1 + (capacity + 1) * entry.encoding.words) state.encoding.words hw state.fits
    have positive := (width_pos hw).ne'
    apply DescriptionFits.seq (width_pos hw) (by simp [DescriptionFits, description, positive]; omega)
    intro token member
    simp only [description, List.mem_cons, List.mem_append] at member
    rcases member with rfl | rfl | member | member
    · omega
    · exact Nat.one_lt_two_pow positive
    · apply continued token
      simpa only [description, List.mem_cons, List.mem_append] using member
    · exact stopped token member

def realizer (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.encoding.words + state.encoding.words + 2 * env.encoding.words < 2 ^ w) :
    Realizer cost (frame entry state env capacity countFits storageFits) state (denote f) where
  code := code body.code body.savedBuffer entry.encoding.words state.encoding.words env.encoding.words capacity
  positive_width := width_pos hw
  description_fits := code_descriptionFits cost allocation entry state env argFits hw body nameFits capacity countFits storageFits
  random_free := code_randomFree _ body.random_free _ _ _ _ _
  time value := time (w := w) cost f body.time body.savedBuffer entry.encoding.words state.encoding.words env.encoding.words capacity value.1.val value.2.1 value.2.2
  net value := time (w := w) cost f body.time body.savedBuffer entry.encoding.words state.encoding.words env.encoding.words capacity value.1.val value.2.1 value.2.2
  workspace value := time (w := w) cost f body.time body.savedBuffer entry.encoding.words state.encoding.words env.encoding.words capacity value.1.val value.2.1 value.2.2
  correct tape value before represented := by
    obtain ⟨after, net, peak, execution, result⟩ :=
      exec cost allocation entry state env argFits hw body nameFits capacity countFits storageFits tape value before represented
    exact ⟨after, net, peak, execution, result, execution.net_le_time allocation, execution.peak_le_time allocation⟩

omit allocation entry state env argFits hw body nameFits in
theorem callerTime_unit_le (buffer input output saved body : Nat) :
    callerTime (w := w) .unit buffer input output saved body ≤ body + 8 * input + 8 * output + 12 * saved := by
  have bound := Assembly.code_time_unit_le (Retain.restoreOperands (w := w) buffer output saved)
  simp only [Retain.restoreOperands, List.length_append, reads_length, CostModel.unit] at bound
  simp only [callerTime, Retain.save, Retain.restoreOperands, Stmt.staticTime, copySlice_staticTime, selectSlice_staticTime, sliceWordTime, CostModel.unit]
  omega

/-- A common width bound for every prepared, retained, or restored frame. -/
def width (entry state env capacity : Nat) : Nat := 1 + (capacity + 1) * entry + state + 2 * env

omit cost allocation entry state env argFits hw body nameFits in
theorem time_unit_le (f : A × (B × E) → B) (bodyTime : A × (B × E) → Nat) (bodyBound : Nat)
    (bounded : ∀ value, bodyTime value ≤ bodyBound) (buffer entry state env capacity : Nat)
    (values : List A) (initial : B) (context : E) :
    time (w := w) .unit f bodyTime buffer entry state env capacity values initial context ≤
      8 * state + capacity * (bodyBound + 44 * width entry state env capacity + 7) := by
  induction capacity generalizing values initial with
  | zero => simp [time, selectSlice_staticTime, sliceWordTime, CostModel.unit]; omega
  | succ capacity ih =>
    let W := width entry state env (capacity + 1)
    have oldWidth : width entry state env capacity ≤ W := by dsimp [width, W]; nlinarith
    have stateWidth : state ≤ W := by dsimp [width, W]; nlinarith
    have argumentWidth : entry + (state + env) ≤ W := by dsimp [width, W]; nlinarith
    have savedWidth : 1 + capacity * entry + env ≤ W := by dsimp [width, W]; nlinarith
    have preparedWidth : prepareWords entry state env capacity ≤ W := by dsimp [prepareWords, width, W]; nlinarith
    have restoredWidth : state + (1 + capacity * entry) + env ≤ W := by dsimp [width, W]; nlinarith
    cases values with
    | nil =>
      simp only [time, selectSlice_staticTime, sliceWordTime, CostModel.unit]
      dsimp [W, width] at *
      nlinarith
    | cons head tail =>
      have prepared := prepare_time_unit_le (w := w) entry state env capacity
      have called := callerTime_unit_le (w := w) buffer (entry + (state + env)) state (1 + capacity * entry + env) (bodyTime (head, initial, context))
      have restored := Reorder.time_unit_le (w := w) state (1 + capacity * entry) env
      have following := ih tail (f (head, initial, context))
      have bodyTimeBound := bounded (head, initial, context)
      have monotone := Nat.mul_le_mul_left capacity (show bodyBound + 44 * width entry state env capacity + 7 ≤ bodyBound + 44 * W + 7 by omega)
      change 1 + (1 + ((prepare (w := w) entry state env capacity).staticTime .unit +
        (callerTime (w := w) .unit buffer (entry + (state + env)) state (1 + capacity * entry + env) (bodyTime (head, initial, context)) +
          ((Assembly.code (Reorder.operands (w := w) state (1 + capacity * entry) env)).staticTime .unit +
            time (w := w) .unit f bodyTime buffer entry state env capacity tail (f (head, initial, context)) context)))) ≤ _
      change _ ≤ 8 * state + (capacity + 1) * (bodyBound + 44 * W + 7)
      rw [Nat.add_mul, Nat.one_mul]
      omega

omit cost allocation entry state env argFits hw body nameFits in
theorem retained_descriptionWords_le (body : Stmt w) (buffer input output saved : Nat) :
    descriptionWords (Retain.code body buffer input output saved) ≤
      descriptionWords body + 26 * input + 26 * output + 39 * saved + 39 := by
  have bound := Assembly.code_descriptionWords_le (Retain.restoreOperands (w := w) buffer output saved)
  simp only [Retain.restoreOperands, List.length_append, reads_length] at bound
  simp only [Retain.code, Retain.restoreOperands, descriptionWords_seq, Retain.save_descriptionWords, selectSlice_descriptionWords]
  simp only [descriptionWords, description, List.length_cons, List.length_nil] at *
  omega

omit cost allocation entry state env argFits hw body nameFits in
theorem code_descriptionWords_le (body : Stmt w) (buffer entry state env capacity : Nat) :
    descriptionWords (code body buffer entry state env capacity) ≤
      26 * state + 14 + capacity * (descriptionWords body + 169 * width entry state env capacity + 115) := by
  induction capacity with
  | zero => simp [code, selectSlice_descriptionWords]
  | succ capacity ih =>
    let W := width entry state env (capacity + 1)
    have oldWidth : width entry state env capacity ≤ W := by dsimp [width, W]; nlinarith
    have stateWidth : state ≤ W := by dsimp [width, W]; nlinarith
    have argumentWidth : entry + (state + env) ≤ W := by dsimp [width, W]; nlinarith
    have savedWidth : 1 + capacity * entry + env ≤ W := by dsimp [width, W]; nlinarith
    have preparedWidth : prepareWords entry state env capacity ≤ W := by dsimp [prepareWords, width, W]; nlinarith
    have restoredWidth : state + (1 + capacity * entry) + env ≤ W := by dsimp [width, W]; nlinarith
    have prepared := prepare_descriptionWords_le (w := w) entry state env capacity
    have called := retained_descriptionWords_le body buffer (entry + (state + env)) state (1 + capacity * entry + env)
    have restored := Reorder.descriptionWords_le (w := w) state (1 + capacity * entry) env
    have monotone := Nat.mul_le_mul_left capacity (show descriptionWords body + 169 * width entry state env capacity + 115 ≤
      descriptionWords body + 169 * W + 115 by omega)
    have branchWords (yes no : Stmt w) : descriptionWords (.ifNZ 1 yes no) =
        descriptionWords yes + descriptionWords no + 2 := by simp [descriptionWords, description]
    have expand : descriptionWords (code body buffer entry state env (capacity + 1)) =
        descriptionWords (prepare (w := w) entry state env capacity) +
        descriptionWords (Retain.code body buffer (entry + (state + env)) state (1 + capacity * entry + env)) +
        descriptionWords (Assembly.code (Reorder.operands (w := w) state (1 + capacity * entry) env)) +
        descriptionWords (code body buffer entry state env capacity) + 26 * state + 24 := by
      rw [code, descriptionWords_seq, branchWords]
      simp only [descriptionWords_seq, selectSlice_descriptionWords]
      have loadWords : descriptionWords (.memLoad 1 0 0 : Stmt w) = 4 := rfl
      rw [loadWords]
      omega
    rw [expand]
    change _ ≤ 26 * state + 14 + (capacity + 1) * (descriptionWords body + 169 * W + 115)
    rw [Nat.add_mul, Nat.one_mul]
    omega

end Signatures.Runtime.CaliperBackend.ListFold
