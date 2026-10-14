import Signatures.Runtime.HeapLoop
import Signatures.Runtime.QueryTreeRel

/-! The binary controller refines source `repeatRun`, preserving every query and
reply path. The invariant relates heap roots, both handler states, and source
values. The cost relation scales actual source steps, not a uniform body price. -/

namespace Signatures.Runtime.HeapLoop

open HeapBits SharedHeap
open PrimeFieldCircuit (exponent)

variable {A S T I : Type} {spec : OracleSpec I}

def ResultRel (Inv : Address → Store → T → A → S → Prop) (factor overhead : Nat)
    (actual : Run HeapExpression.Result × T) (source : Run A × S) : Prop :=
  ∃ root heap, actual.1.value = some (root, heap) ∧ Inv root heap actual.2 source.1.value source.2 ∧
    actual.1.steps ≤ source.1.steps*factor + overhead

theorem run_refines
    (step : Address → Store → StateT T (OracleComp spec) (Run HeapExpression.Result))
    (source : A → StateT S (OracleComp spec) (Run A))
    (Inv : Nat → Address → Store → T → A → S → Prop) (nodes factor overhead : Nat)
    (haddr : ∀ root heap impl x state, Inv 0 root heap impl x state → root.length ≤ nodes)
    (hstep : ∀ n root heap impl x state, Inv (n+1) root heap impl x state →
      QueryTreeRel (ResultRel (Inv n) factor overhead) ((step root heap).run impl) ((source x).run state))
    (bits : List Bool) (acc : Address) (heap : Store) (impl : T) (x : A) (state : S)
    (hi : Inv (exponent bits) acc heap impl x state)
    (hfactor : 2*bits.length + 2*nodes + overhead + 3 ≤ factor) :
    QueryTreeRel (ResultRel (Inv 0) factor 0) ((run step bits acc heap).run impl)
      ((repeatRun source (exponent bits) x).run state) := by
  generalize hn : exponent bits = n at hi ⊢
  induction n generalizing bits acc heap impl x state with
  | zero =>
    rw [run]
    dsimp only
    split
    · simp only [repeatRun, StateT.run_pure]
      apply QueryTreeRel.pure
      refine ⟨acc, heap, by simp only [copy_value], hi, ?_⟩
      have ha := haddr acc heap impl x state hi
      simp only [tick_steps, copy_steps, Nat.one_mul, Nat.add_zero]
      omega
    · rename_i rest ht
      have h := (tick_some ht).2
      omega
  | succ n ih =>
    rw [run]
    dsimp only
    split
    · rename_i ht
      have h := tick_none ht
      omega
    · rename_i rest ht
      have hrest := tick_some ht
      have hn' : exponent rest = n := by omega
      simp only [repeatRun, StateT.run_bind, StateT.run_pure]
      apply (hstep n acc heap impl x state hi).bind
      intro actual reference hrel
      rcases actual with ⟨body, nextImpl⟩
      rcases reference with ⟨ref, nextState⟩
      obtain ⟨root, nextHeap, hv, hinv, hc⟩ := hrel
      dsimp only at hv hinv hc
      simp only [hv, StateT.run_bind, StateT.run_pure]
      have htail := ih rest root nextHeap nextImpl ref.value nextState
        (by rw [hrest.1]; exact hfactor) hn' hinv
      apply htail.bind
      intro actual reference hrel
      rcases actual with ⟨out, finalImpl⟩
      rcases reference with ⟨refOut, finalState⟩
      obtain ⟨result, finalHeap, hout, hfinal, hcost⟩ := hrel
      dsimp only at hout hfinal hcost
      apply QueryTreeRel.pure
      refine ⟨result, finalHeap, hout, hfinal, ?_⟩
      simp only [tick_steps, Nat.add_zero] at hc hcost ⊢
      nlinarith

end Signatures.Runtime.HeapLoop
