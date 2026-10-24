import Proofs.Runtime.Caliper.FoldStep

/-! Word acceptance, exact execution profiles and uniform resource bounds for a
fold stage whose input and output accumulator layouts may differ. -/

namespace Signatures.Runtime.CaliperBackend.FoldStep

open Caliper Assembly

variable {w : Nat} {A B D E R : Type}

/-- A common upper bound for all frames in one stage, including both
accumulator representations. It need not itself be allocated. -/
def width (entry state next env capacity : Nat) : Nat :=
  1 + (capacity + 1) * entry + state + next + 2 * env

theorem time_unit_le {capacity : Nat} (f : A × (B × E) → D)
    (bodyTime : A × (B × E) → Nat) (followingTime : BoundedList A capacity × (D × E) → Nat)
    (stopTime : B → Nat) (bodyBound followingBound stopBound : Nat)
    (bodyBounded : ∀ value, bodyTime value ≤ bodyBound)
    (followingBounded : ∀ value, followingTime value ≤ followingBound)
    (stopBounded : ∀ value, stopTime value ≤ stopBound)
    (buffer entry state next env : Nat) (value : BoundedList A (capacity + 1) × (B × E)) :
    time (w := w) .unit f bodyTime followingTime stopTime buffer entry state next env value ≤
      bodyBound + followingBound + stopBound + 44 * width entry state next env capacity + 7 := by
  let W := width entry state next env capacity
  have stateWidth : state ≤ W := by dsimp [width, W]; nlinarith
  have nextWidth : next ≤ W := by dsimp [width, W]; nlinarith
  have argumentWidth : entry + (state + env) ≤ W := by dsimp [width, W]; nlinarith
  have savedWidth : 1 + capacity * entry + env ≤ W := by dsimp [width, W]; nlinarith
  have preparedWidth : ListFold.prepareWords entry state env capacity ≤ W := by dsimp [ListFold.prepareWords, width, W]; nlinarith
  have restoredWidth : next + (1 + capacity * entry) + env ≤ W := by dsimp [width, W]; nlinarith
  rcases value with ⟨⟨values, valid⟩, accumulator, context⟩
  cases values with
  | nil =>
    have stopped := stopBounded accumulator
    simp only [time, selectSlice_staticTime, sliceWordTime, CostModel.unit]
    change _ ≤ bodyBound + followingBound + stopBound + 44 * W + 7
    omega
  | cons head tail =>
    have prepared := ListFold.prepare_time_unit_le (w := w) entry state env capacity
    have called := ListFold.callerTime_unit_le (w := w) buffer (entry + (state + env)) next (1 + capacity * entry + env) (bodyTime (head, accumulator, context))
    have restored := Reorder.time_unit_le (w := w) next (1 + capacity * entry) env
    have bodyTimeBound := bodyBounded (head, accumulator, context)
    have followingTimeBound := followingBounded (⟨tail, by simpa using valid⟩, f (head, accumulator, context), context)
    change 1 + (1 + ((ListFold.prepare (w := w) entry state env capacity).staticTime .unit +
      (ListFold.callerTime (w := w) .unit buffer (entry + (state + env)) next (1 + capacity * entry + env) (bodyTime (head, accumulator, context)) +
        ((Assembly.code (Reorder.operands (w := w) next (1 + capacity * entry) env)).staticTime .unit +
          followingTime (⟨tail, by simpa using valid⟩, f (head, accumulator, context), context))))) ≤
            bodyBound + followingBound + stopBound + 44 * W + 7
    omega

theorem code_descriptionWords_le (body following stop : Stmt w) (buffer entry state next env capacity : Nat) :
    descriptionWords (code body following stop buffer entry state next env capacity) ≤
      descriptionWords body + descriptionWords following + descriptionWords stop +
        169 * width entry state next env capacity + 116 := by
  let W := width entry state next env capacity
  have stateWidth : state ≤ W := by dsimp [width, W]; nlinarith
  have nextWidth : next ≤ W := by dsimp [width, W]; nlinarith
  have argumentWidth : entry + (state + env) ≤ W := by dsimp [width, W]; nlinarith
  have savedWidth : 1 + capacity * entry + env ≤ W := by dsimp [width, W]; nlinarith
  have preparedWidth : ListFold.prepareWords entry state env capacity ≤ W := by dsimp [ListFold.prepareWords, width, W]; nlinarith
  have restoredWidth : next + (1 + capacity * entry) + env ≤ W := by dsimp [width, W]; nlinarith
  have prepared := ListFold.prepare_descriptionWords_le (w := w) entry state env capacity
  have called := ListFold.retained_descriptionWords_le body buffer (entry + (state + env)) next (1 + capacity * entry + env)
  have restored := Reorder.descriptionWords_le (w := w) next (1 + capacity * entry) env
  have branchWords (yes no : Stmt w) : descriptionWords (.ifNZ 1 yes no) =
      descriptionWords yes + descriptionWords no + 2 := by simp [descriptionWords, description]
  have expand : descriptionWords (code body following stop buffer entry state next env capacity) =
      descriptionWords (ListFold.prepare (w := w) entry state env capacity) +
      descriptionWords (Retain.code body buffer (entry + (state + env)) next (1 + capacity * entry + env)) +
      descriptionWords (Assembly.code (Reorder.operands (w := w) next (1 + capacity * entry) env)) +
      descriptionWords following + descriptionWords stop + 26 * state + 25 := by
    rw [code, descriptionWords_seq, branchWords]
    simp only [descriptionWords_seq, selectSlice_descriptionWords]
    have loadWords : descriptionWords (.memLoad 1 0 0 : Stmt w) = 4 := rfl
    rw [loadWords]
    omega
  rw [expand]
  change _ ≤ descriptionWords body + descriptionWords following + descriptionWords stop + 169 * W + 116
  omega

variable (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Representation w A) (state : Representation w B) (next : Representation w D)
    (env : Representation w E) (output : Representation w R) (capacity : Nat)
    (hw : 16 < 2 ^ w) (countFits : capacity + 1 < 2 ^ w)
    (argFits : entry.encoding.words + state.encoding.words + env.encoding.words < 2 ^ w)
    (inputFits : 1 + (capacity + 1) * entry.encoding.words + state.encoding.words + 2 * env.encoding.words < 2 ^ w)
    (nextFits : 1 + capacity * entry.encoding.words + next.encoding.words + 2 * env.encoding.words < 2 ^ w)
    {f : A × (B × E) → D} {g : BoundedList A capacity × (D × E) → R} {h : B → R}
    (body : Realizer cost (ListFold.argument entry state env argFits) next f)
    (following : Realizer cost (ListFold.frame entry next env capacity (by omega) nextFits) output g)
    (stop : Realizer cost state output h) (nameFits : body.savedBuffer < 2 ^ w)

include allocation hw nameFits inputFits in
theorem descriptionFits : DescriptionFits
    (code body.code following.code stop.code body.savedBuffer entry.encoding.words state.encoding.words next.encoding.words env.encoding.words capacity) := by
  let savedRep := ListFold.saved entry env capacity (by omega) (by nlinarith)
  have retained : DescriptionFits (Retain.code body.code body.savedBuffer
      (entry.encoding.words + (state.encoding.words + env.encoding.words)) next.encoding.words
      (1 + capacity * entry.encoding.words + env.encoding.words)) :=
    (body.retain allocation savedRep hw nameFits (by
      change (entry.encoding.words + (state.encoding.words + env.encoding.words)) +
        (1 + capacity * entry.encoding.words + env.encoding.words) < 2 ^ w
      nlinarith) (by
      change next.encoding.words + (1 + capacity * entry.encoding.words + env.encoding.words) < 2 ^ w
      nlinarith)).description_fits
  have rearranged := Assembly.code_descriptionFits
    (Reorder.operands (w := w) next.encoding.words (1 + capacity * entry.encoding.words) env.encoding.words) hw
    (by rw [Reorder.operands_length]; nlinarith) (Reorder.operands_names _ _ _)
  have continued := DescriptionFits.seq (width_pos hw)
    (ListFold.prepare_descriptionFits _ _ _ _ hw inputFits)
    (DescriptionFits.seq (width_pos hw) retained
      (DescriptionFits.seq (width_pos hw) rearranged following.description_fits))
  have stopped := DescriptionFits.seq (width_pos hw)
    (selectSlice_descriptionFits (w := w) (1 + (capacity + 1) * entry.encoding.words) state.encoding.words hw state.fits)
    stop.description_fits
  apply DescriptionFits.seq (width_pos hw) (by simp [DescriptionFits, description, (width_pos hw).ne']; omega)
  intro token member
  simp only [description, List.mem_cons, List.mem_append] at member
  rcases member with rfl | rfl | member | member
  · omega
  · exact Nat.one_lt_two_pow (width_pos hw).ne'
  · apply continued token
    simpa only [description, List.mem_cons, List.mem_append] using member
  · apply stopped token
    simpa only [description, List.mem_cons, List.mem_append] using member

def realizer : Realizer cost (ListFold.frame entry state env (capacity + 1) countFits inputFits) output (result f g h) where
  code := code body.code following.code stop.code body.savedBuffer entry.encoding.words state.encoding.words next.encoding.words env.encoding.words capacity
  positive_width := width_pos hw
  description_fits := descriptionFits cost allocation entry state next env output capacity hw countFits argFits inputFits nextFits body following stop nameFits
  random_free := by
    simp [code, Stmt.RandomFree, ListFold.prepare_randomFree, Retain.code, Retain.save_randomFree,
      selectSlice_randomFree, Assembly.code_randomFree, body.random_free, following.random_free, stop.random_free]
  time := time (w := w) cost f body.time following.time stop.time body.savedBuffer entry.encoding.words state.encoding.words next.encoding.words env.encoding.words
  net value := time (w := w) cost f body.time following.time stop.time body.savedBuffer entry.encoding.words state.encoding.words next.encoding.words env.encoding.words value
  workspace value := time (w := w) cost f body.time following.time stop.time body.savedBuffer entry.encoding.words state.encoding.words next.encoding.words env.encoding.words value
  correct tape value before represented := by
    obtain ⟨after, net, peak, execution, outputValue⟩ :=
      exec cost allocation entry state next env output capacity hw countFits argFits inputFits nextFits body following stop nameFits tape value before represented
    exact ⟨after, net, peak, execution, outputValue, execution.net_le_time allocation, execution.peak_le_time allocation⟩

end Signatures.Runtime.CaliperBackend.FoldStep
