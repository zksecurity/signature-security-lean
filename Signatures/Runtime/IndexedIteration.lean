import Signatures.Runtime.Program
import Mathlib.Data.List.GetD

/-! A bounded indexed loop traverses the original list in order. The semantic
lemma permits arbitrary effects, so both replies and effect state are retained.
It does not give free indexing or length computation to an implementation. -/

namespace Signatures.Runtime

variable {m : Type → Type} [Monad m] [LawfulMonad m] {A B : Type}

def indexedStep (action : A → B → m B) (xs : List A) (default : A) (state : Nat × B) : m (Nat × B) := do
  let next ← action ((xs[state.1]?).getD default) state.2
  pure (state.1 + 1, next)

theorem repeat_indexed_suffix (action : A → B → m B) (xs : List A) (default : A)
    (suffix : List A) (n : Nat) (acc : B) (hs : xs.drop n = suffix) :
    repeatDenote (indexedStep action xs default) suffix.length (n, acc) =
      (fun value => (n + suffix.length, value)) <$> suffix.foldlM (fun acc x => action x acc) acc := by
  induction suffix generalizing n acc with
  | nil => simp [repeatDenote]
  | cons x suffix ih =>
      have hx : xs[n]? = some x := by simpa only [List.head?_drop, List.head?_cons] using congrArg List.head? hs
      have ht : xs.drop (n + 1) = suffix := by
        simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail hs
      simp only [List.length_cons, repeatDenote, indexedStep, hx, Option.getD_some,
        bind_assoc, pure_bind, List.foldlM_cons, map_bind]
      congr 1
      funext value
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1) value ht

theorem repeat_indexed (action : A → B → m B) (xs : List A) (default : A) (acc : B) :
    repeatDenote (indexedStep action xs default) xs.length (0, acc) =
      (fun value => (xs.length, value)) <$> xs.foldlM (fun acc x => action x acc) acc := by
  simpa only [Nat.zero_add] using repeat_indexed_suffix action xs default xs 0 acc (by simp)

end Signatures.Runtime
