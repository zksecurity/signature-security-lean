import Proofs.Runtime.HeapProgram
import Proofs.Runtime.ProgramTrace
import Proofs.Runtime.QueryTreeRel

/-! Stateful program results on the shared heap. Allocation growth is tied to
the matched source execution, not an assumed maximum final heap size. -/

namespace Signatures.Runtime.HeapProgram

open HeapBits SharedHeap OracleComp
open PrimeFieldCircuit (exponent)

variable {base : CryptoAtom → Type} {S T I : Type} {spec : OracleSpec I}
  {w cap : Nat} {leaf : (a : CryptoAtom) → List Bool → base a → Prop}

def Post (w cap : Nat) (leaf : (a : CryptoAtom) → List Bool → base a → Prop)
    (StateRel : List Node → T → S → Prop) (heap : List Node) (allocations : Nat)
    {a : Ty CryptoAtom} (actual : Run HeapExpression.Result × T) (source : Run (a.Value base) × S) : Prop :=
  ∃ extra root store, actual.1.value = some (root, store) ∧ store.Represents (heap ++ extra) ∧
    WellFormed cap (heap ++ extra) ∧ Represents w leaf (heap ++ extra) a root source.1.value ∧
    StateRel (heap ++ extra) actual.2 source.2 ∧ extra.length ≤ allocations

theorem Post.mono {StateRel : List Node → T → S → Prop} {heap : List Node} {n m : Nat}
    {a : Ty CryptoAtom} {actual : Run HeapExpression.Result × T} {source : Run (a.Value base) × S}
    (h : Post w cap leaf StateRel heap n actual source) (hn : n ≤ m) :
    Post w cap leaf StateRel heap m actual source := by
  obtain ⟨extra, root, store, hv, hs, hw, hx, hi, hlen⟩ := h
  exact ⟨extra, root, store, hv, hs, hw, hx, hi, hlen.trans hn⟩

theorem Post.rebase {StateRel : List Node → T → S → Prop} {heap added : List Node} {n : Nat}
    {a : Ty CryptoAtom} {actual : Run HeapExpression.Result × T} {source : Run (a.Value base) × S}
    (h : Post w cap leaf StateRel (heap ++ added) n actual source) :
    Post w cap leaf StateRel heap (added.length+n) actual source := by
  obtain ⟨extra, root, store, hv, hs, hw, hx, hi, hlen⟩ := h
  refine ⟨added ++ extra, root, store, hv, ?_, ?_, ?_, ?_, by simp; omega⟩
  · simpa only [List.append_assoc] using hs
  · simpa only [List.append_assoc] using hw
  · simpa only [List.append_assoc] using hx
  · simpa only [List.append_assoc] using hi

theorem Post.state_mono {StateRel Other : List Node → T → S → Prop} {heap : List Node} {n : Nat}
    {a : Ty CryptoAtom} {actual : Run HeapExpression.Result × T} {source : Run (a.Value base) × S}
    (h : Post w cap leaf StateRel heap n actual source)
    (hi : ∀ extra, StateRel (heap ++ extra) actual.2 source.2 → Other (heap ++ extra) actual.2 source.2) :
    Post w cap leaf Other heap n actual source := by
  obtain ⟨extra, root, store, hv, hs, hw, hx, hstate, hlen⟩ := h
  exact ⟨extra, root, store, hv, hs, hw, hx, hi extra hstate, hlen⟩

/-- Allocation-sensitive refinement for the implemented binary controller.
The source trace determines which body obligations are needed after each reply. -/
theorem loop_refines {a : Ty CryptoAtom}
    (StateRel : List Node → T → S → Prop)
    (step : Address → Store → StateT T (OracleComp spec) (Run HeapExpression.Result))
    (source : a.Value base → StateT S (OracleComp spec) (Run (a.Value base)))
    (check : a.Value base → S → Prop)
    (hstep : ∀ heap root store impl x state, store.Represents heap → WellFormed cap heap →
      Represents w leaf heap a root x → StateRel heap impl state → check x state →
      QueryTreeRel (fun actual source => Post w cap leaf StateRel heap source.1.steps actual source)
        ((step root store).run impl) ((source x).run state))
    (heap : List Node) (root : Address) (store : Store) (impl : T) (x : a.Value base) (state : S)
    (hs : store.Represents heap) (hw : WellFormed cap heap) (hx : Represents w leaf heap a root x)
    (hi : StateRel heap impl state) (bits : List Bool)
    (ht : NaturalRange.RepeatTrace check source (exponent bits) x state) :
    QueryTreeRel (fun actual source => Post w cap leaf StateRel heap source.1.steps actual source)
      ((HeapLoop.run step bits root store).run impl) ((repeatRun source (exponent bits) x).run state) := by
  generalize hn : exponent bits = n at ht ⊢
  induction n generalizing bits heap root store impl x state with
  | zero =>
    rw [HeapLoop.run]
    dsimp only
    split
    · simp only [repeatRun, StateT.run_pure]
      apply QueryTreeRel.pure
      refine ⟨[], root, store, by simp only [copy_value], ?_, ?_, ?_, ?_, by simp⟩
      · simpa using hs
      · simpa using hw
      · simpa using hx
      · simpa using hi
    · rename_i rest htick
      have h := (HeapLoop.tick_some htick).2
      omega
  | succ n ih =>
    rw [HeapLoop.run]
    dsimp only
    split
    · rename_i htick
      have h := HeapLoop.tick_none htick
      omega
    · rename_i rest htick
      have hn' : exponent rest = n := by have h := (HeapLoop.tick_some htick).2; omega
      simp only [repeatRun, StateT.run_bind, StateT.run_pure]
      apply (hstep heap root store impl x state hs hw hx hi ht.1).bind_support
      intro actual _ reference hreference hrel
      rcases actual with ⟨body, nextImpl⟩
      rcases reference with ⟨ref, nextState⟩
      obtain ⟨extra, acc, next, hv, hs₁, hw₁, hx₁, hi₁, hlen⟩ := hrel
      dsimp only at hv hs₁ hw₁ hx₁ hi₁ hlen
      simp only [hv, StateT.run_bind, StateT.run_pure]
      have htail := ih (heap ++ extra) acc next nextImpl ref.value nextState
        hs₁ hw₁ hx₁ hi₁ rest hn' (ht.2 (ref, nextState) hreference)
      apply htail.bind
      intro actual reference hrel
      rcases actual with ⟨out, finalImpl⟩
      rcases reference with ⟨refOut, finalState⟩
      obtain ⟨more, result, finalHeap, hout, hs₂, hw₂, hx₂, hi₂, hmore⟩ := hrel
      dsimp only at hout hs₂ hw₂ hx₂ hi₂ hmore
      apply QueryTreeRel.pure
      refine ⟨extra ++ more, result, finalHeap, hout, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [List.append_assoc] using hs₂
      · simpa only [List.append_assoc] using hw₂
      · simpa only [List.append_assoc] using hx₂
      · simpa only [List.append_assoc] using hi₂
      · simp only [List.length_append]; omega

end Signatures.Runtime.HeapProgram
