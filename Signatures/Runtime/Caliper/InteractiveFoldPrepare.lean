import Signatures.Runtime.Caliper.ListFoldBounds
import Signatures.Runtime.Caliper.InteractiveInvariantBounds
import Signatures.Runtime.Caliper.BufferBounds

/-! Executed frames for an effectful list fold. The nonempty preparer copies
the head, accumulator and tail and decrements the stored tail length. Its
nonempty domain comes from the runtime length branch, not from a free test. -/
namespace Signatures.Runtime.CaliperBackend.InteractiveFold
open Caliper
variable {w : Nat} {A B : Type}

def frame (entry : Representation w A) (state : Representation w B) (capacity : Nat)
    (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.encoding.words + state.encoding.words < 2 ^ w) :
    Representation w (BoundedList A capacity × B) :=
  (entry.boundedList capacity countFits (by omega)).prod state storageFits

def nonempty (capacity : Nat) (value : BoundedList A capacity × B) : Prop := 0 < value.1.val.length
instance (capacity : Nat) (value : BoundedList A capacity × B) : Decidable (nonempty capacity value) :=
  inferInstanceAs (Decidable (0 < value.1.val.length))

def prepared {capacity : Nat} (value : {value : BoundedList A (capacity + 1) × B // nonempty (capacity + 1) value}) :
    (A × B) × BoundedList A capacity :=
  match value with
  | ⟨(⟨[], _⟩, _), valid⟩ => False.elim (Nat.lt_irrefl 0 valid)
  | ⟨(⟨head :: tail, valid⟩, accumulator), _⟩ => ((head, accumulator), ⟨tail, by simpa using valid⟩)

variable (entry : Representation w A) (state : Representation w B) (hw : 16 < 2 ^ w)
    (argFits : entry.encoding.words + state.encoding.words < 2 ^ w)

def finish (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.encoding.words + state.encoding.words < 2 ^ w) :
    Realizer .unit (frame entry state capacity countFits storageFits) state Prod.snd :=
  secondRealizer .unit (by decide) (entry.boundedList capacity countFits (by omega)) state hw storageFits

@[simp] theorem finish_code (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.encoding.words + state.encoding.words < 2 ^ w) :
    (finish entry state hw capacity countFits storageFits).code =
      selectSlice (1 + capacity * entry.encoding.words) state.encoding.words := rfl

variable (capacity : Nat) (countFits : capacity + 1 < 2 ^ w)
    (storageFits : 1 + (capacity + 1) * entry.encoding.words + state.encoding.words < 2 ^ w)

def argument : Representation w (A × B) := entry.prod state argFits
def saved : Representation w (BoundedList A capacity) := entry.boundedList capacity (by omega) (by nlinarith)
def preparedFrame : Representation w ((A × B) × BoundedList A capacity) :=
  (argument entry state argFits).prod (saved entry state capacity countFits storageFits) (by
    change (entry.encoding.words + state.encoding.words) + (1 + capacity * entry.encoding.words) < 2 ^ w
    nlinarith)

def prepare : Realizer .unit
    ((frame entry state (capacity + 1) countFits storageFits).restrict (nonempty (capacity + 1)))
    (preparedFrame entry state argFits capacity countFits storageFits) prepared where
  code := ListFold.prepare entry.encoding.words state.encoding.words 0 capacity
  positive_width := width_pos hw
  description_fits := ListFold.prepare_descriptionFits _ _ _ _ hw (by simpa [ListFold.prepareWords] using storageFits)
  random_free := ListFold.prepare_randomFree _ _ _ _
  time _ := (ListFold.prepare (w := w) entry.encoding.words state.encoding.words 0 capacity).staticTime .unit
  net _ := (ListFold.prepare (w := w) entry.encoding.words state.encoding.words 0 capacity).staticTime .unit
  workspace _ := (ListFold.prepare (w := w) entry.encoding.words state.encoding.words 0 capacity).staticTime .unit
  correct tape value before represented := by
    rcases value with ⟨⟨⟨values, bounded⟩, accumulator⟩, nonempty⟩
    cases values with
    | nil => exact False.elim (Nat.lt_irrefl 0 nonempty)
    | cons head tail =>
      have tailBound : tail.length ≤ capacity := by simpa using bounded
      let payload := entry.encoding.pack tail ++ List.replicate ((capacity - tail.length) * entry.encoding.words) 0
      have payloadSize : payload.length = capacity * (entry.encoding.encode head).length := by
        simp only [payload, List.length_append, Encoding.pack_length, List.length_replicate, entry.encoding.encode_length]
        rw [← Nat.add_mul, Nat.add_sub_of_le tailBound]
      have stored : (before.bufs 0).toList = BitVec.ofNat w (tail.length + 1) ::
          (entry.encoding.encode head ++ payload ++ state.encoding.encode accumulator ++ []) := by
        simpa [frame, Representation.restrict, Encoding.restrict, Representation.prod, Encoding.prod,
          Representation.boundedList, Encoding.boundedList, Encoding.checked, Encoding.pack, payload, List.append_assoc] using represented.2.1
      obtain ⟨after, elapsed, net, peak, execution, contents, offset, capacities⟩ :=
        ListFold.prepare_exec .unit tape (entry.encoding.encode head) payload (state.encoding.encode accumulator)
          [] tail.length capacity payloadSize before stored
          (by simpa [ListFold.prepareWords, entry.encoding.encode_length, state.encoding.encode_length] using storageFits)
          represented.2.2.2
      rw [entry.encoding.encode_length, state.encoding.encode_length, List.length_nil] at execution
      have elapsed_eq := execution.straight_time_eq (ListFold.prepare_straight _ _ _ _)
      subst elapsed
      refine ⟨after, net, peak, execution, ⟨offset.trans represented.1, ?_, execution.wellFormed_preserved represented.2.2.1, capacities⟩,
        execution.net_le_time (by decide), execution.peak_le_time (by decide)⟩
      simpa [preparedFrame, argument, saved, prepared, Representation.prod, Encoding.prod,
        Representation.boundedList, Encoding.boundedList, Encoding.checked, payload, List.append_assoc] using contents

end Signatures.Runtime.CaliperBackend.InteractiveFold
