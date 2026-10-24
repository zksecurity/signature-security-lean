import Proofs.Runtime.Caliper.StagedFoldAcceptance
import Proofs.Runtime.Caliper.FoldNames
import Proofs.Runtime.Caliper.EncodedConstant
import Mathlib.Data.List.Fold

/-! Executed reversal of bounded source lists. Each fold stage grows a represented
accumulator by one slot; early return executes padding to the final capacity.
No enumeration of the entry type and no host-language reversal is executed. -/

namespace Signatures.Runtime.CaliperBackend.ListReverse
open Caliper BoundedSource

structure Layouts (w : Nat) (A : Type) where
  entry : Layout w A
  capacity : Nat
  wordFits : 16 < 2 ^ w
  countFits : capacity < 2 ^ w
  storageFits : 4 * (1 + (capacity + 1) * entry.representation.encoding.words) < 2 ^ w

variable {w : Nat} {A : Type} (layout : Layouts w A)

def Layouts.width : Nat := 1 + (layout.capacity + 1) * layout.entry.representation.encoding.words

def Layouts.list : Layout w (List A) :=
  layout.entry.boundedList layout.capacity layout.countFits (by have := layout.storageFits; nlinarith)

def Layouts.env (_layout : Layouts w A) : Layout w Unit := DataImplementation.unitLayout w

def Layouts.states (i : Fin (layout.capacity + 1)) : Layout w (List A) :=
  layout.entry.boundedList i.val (by have := layout.countFits; omega) (by
    have := layout.storageFits
    have bound : i.val ≤ layout.capacity := by omega
    have := Nat.mul_le_mul_right layout.entry.representation.encoding.words bound
    nlinarith)

theorem Layouts.argFits (i : Fin layout.capacity) :
    layout.entry.representation.encoding.words + (layout.states i.castSucc).representation.encoding.words +
      layout.env.representation.encoding.words < 2 ^ w := by
  change layout.entry.representation.encoding.words + (1 + i.val * layout.entry.representation.encoding.words) + 0 < 2 ^ w
  have := layout.storageFits
  have := Nat.mul_le_mul_right layout.entry.representation.encoding.words (show i.val ≤ layout.capacity by omega)
  nlinarith

theorem Layouts.frameFits (i : Fin (layout.capacity + 1)) :
    1 + (layout.capacity - i.val) * layout.entry.representation.encoding.words + (layout.states i).representation.encoding.words +
      2 * layout.env.representation.encoding.words < 2 ^ w := by
  change 1 + (layout.capacity - i.val) * layout.entry.representation.encoding.words +
    (1 + i.val * layout.entry.representation.encoding.words) + 2 * 0 < 2 ^ w
  have combined : (layout.capacity - i.val) * layout.entry.representation.encoding.words +
      i.val * layout.entry.representation.encoding.words = layout.capacity * layout.entry.representation.encoding.words := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
  have := layout.storageFits
  nlinarith

def Layouts.frame := FoldImplementation.input layout.entry (layout.states 0) layout.env layout.capacity
  layout.countFits (layout.frameFits 0)

def step (value : A × (List A × Unit)) : List A := value.1 :: value.2.1

def body (i : Fin layout.capacity) : Implementation .unit
    (FoldImplementation.bodyInput layout.entry (layout.states i.castSucc) layout.env (layout.argFits i)) (layout.states i.succ) step where
  preserves value valid := ⟨by simpa only [step, List.length_cons, Fin.val_castSucc, Fin.val_succ] using Nat.add_le_add_right valid.2.1.1 1,
    by intro entry member; rcases List.mem_cons.mp member with rfl | member
       · exact valid.1
       · exact valid.2.1.2 entry member⟩
  program := (ListData.cons .unit (by decide) layout.entry i.val layout.wordFits
    (by have := layout.countFits; omega) (layout.states i.succ).representation.fits).program.viewInput
      (FoldImplementation.bodyInput layout.entry (layout.states i.castSucc) layout.env (layout.argFits i)).representation
      (fun value => ⟨(value.val.1, value.val.2.1), value.property.1, value.property.2.1⟩) (by
        intro value
        change _ ++ (_ ++ []) = _ ++ _
        rw [List.append_nil]
        rfl)

def stop (i : Fin (layout.capacity + 1)) : Implementation .unit (layout.states i) layout.list id :=
  ListData.widen .unit (by decide) layout.entry i.val layout.capacity (by omega) layout.wordFits layout.countFits
    layout.list.representation.fits

theorem body_buffers (i : Fin layout.capacity) : (body layout i).program.code.memBound ≤ 2 := by
  have built := (Assembly.code_names (ListConstruct.consOperands (w := w) layout.entry.representation.encoding.words i.val) 1 (by
    simp only [ListConstruct.consOperands, Assembly.sourcesBound_append]
    exact ⟨⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩,
      Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩)).2
  have increment := CellArithmetic.buffers (w := w) 0 .add 1
  change max _ _ ≤ 2
  exact max_le built (increment.trans (by decide))

theorem stop_buffers (i : Fin (layout.capacity + 1)) : (stop layout i).program.code.memBound ≤ 2 :=
  (Assembly.code_names _ 1 ((Assembly.sourcesBound_append _ _ _).mpr
    ⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_replicate _ _ _⟩)).2

def compiled := StagedFold.compile (by decide) layout.entry layout.list layout.env layout.wordFits step
  layout.capacity layout.states layout.countFits layout.argFits layout.frameFits (fun i => some (body layout i)) (stop layout)

theorem accepted : (compiled layout).isSome := by
  obtain ⟨implementation, equal, _⟩ := StagedFold.accept (by decide) layout.entry layout.list layout.env layout.wordFits step
    layout.capacity layout.states layout.countFits layout.argFits layout.frameFits (body layout) (stop layout)
    2 2 (body_buffers layout) (stop_buffers layout) (by have := layout.wordFits; omega)
  rw [compiled, equal]
  rfl

def loop : Implementation .unit layout.frame layout.list (FoldImplementation.sourceFold step) :=
  (compiled layout).get (accepted layout)

theorem loop_buffers : (loop layout).program.code.memBound ≤ 3 := by
  obtain ⟨implementation, equal, bounded⟩ := StagedFold.accept (by decide) layout.entry layout.list layout.env layout.wordFits step
    layout.capacity layout.states layout.countFits layout.argFits layout.frameFits (body layout) (stop layout)
    2 2 (body_buffers layout) (stop_buffers layout) (by have := layout.wordFits; omega)
  have same : loop layout = implementation := Option.get_of_eq_some (accepted layout) equal
  rw [same]
  exact bounded

def initial : (layout.states 0).Value := ⟨[], by exact ⟨by simp, by simp⟩⟩
def saved : Layout w (List A × Unit) := (layout.states 0).prod layout.env (by
  change (1 + 0 * layout.entry.representation.encoding.words) + 0 < 2 ^ w
  have := layout.wordFits
  omega)
def empty : (saved layout).Value := ⟨([], ()), (initial layout).property, trivial⟩
def prepare : Implementation .unit layout.list layout.frame (fun values => (values, [], ())) :=
  (Implementation.identity layout.list (width_pos layout.wordFits)).pair
    (Implementation.constant layout.list (saved layout) (empty layout) layout.wordFits) (by decide) layout.wordFits
    (by have := layout.wordFits; change max 2 0 < 2 ^ w; omega)
    (by have := Implementation.constant_buffers layout.list (saved layout) (empty layout) layout.wordFits
        have := layout.wordFits; dsimp only [Realizer.savedBuffer]; omega)
    (by change (1 + layout.capacity * _) + (1 + layout.capacity * _) < 2 ^ w; have := layout.storageFits; nlinarith)
    (by change (1 + layout.capacity * _) + (1 + layout.capacity * _) < 2 ^ w; have := layout.storageFits; nlinarith)
    (by change (1 + layout.capacity * _) + (1 + 0 * _ + 0) < 2 ^ w; have := layout.storageFits; nlinarith)

theorem reverse_fold (values : List A) : FoldImplementation.sourceFold step (values, [], ()) = values.reverse := by
  change values.foldl (fun accumulated value => value :: accumulated) [] = values.reverse
  exact List.foldl_cons_nil (l := values)

def implementation : Implementation .unit layout.list layout.list List.reverse where
  preserves values valid := ⟨by simpa only [List.length_reverse] using valid.1,
    fun value member => valid.2 value (List.mem_reverse.mp member)⟩
  program := ((prepare layout).then (loop layout)).program.viewOutput _ _ (by
    intro value
    apply congrArg layout.list.representation.encoding.encode
    apply Subtype.ext
    exact (reverse_fold value.val).symm)

end Signatures.Runtime.CaliperBackend.ListReverse
