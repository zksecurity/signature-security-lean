import Signatures.Runtime.HeapExpressionRefinement
import Signatures.Runtime.Program

/-! A binary loop counter and effectful shared-heap controller. The natural
value of the counter is used only in proofs and the erased termination measure;
online control tests/decrements the actual bits and charges every copied cell. -/

namespace Signatures.Runtime.HeapLoop

open HeapBits SharedHeap
open PrimeFieldCircuit (exponent)

/-- `none` means zero; otherwise return the same-width predecessor. -/
def tick : List Bool → Run (Option (List Bool))
  | [] => ⟨none, 1⟩
  | false :: bits => let r := tick bits; ⟨r.value.map (true :: ·), r.steps + 2⟩
  | true :: bits => let r := HeapBits.copy bits; ⟨some (false :: r.value), r.steps + 2⟩

theorem tick_steps (bits : List Bool) : (tick bits).steps = 2*bits.length+1 := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [tick, copy_steps, ih] <;> omega

theorem tick_spec (bits : List Bool) :
    match (tick bits).value with
    | none => exponent bits = 0
    | some rest => rest.length = bits.length ∧ exponent bits = exponent rest + 1 := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    cases b with
    | false =>
      cases ht : (tick bits).value with
      | none => simpa [tick, ht, exponent] using ih
      | some rest =>
        simp only [ht] at ih
        simp only [tick, ht, Option.map_some, List.length_cons, exponent, Bool.toNat_false,
          Bool.toNat_true]
        exact ⟨by omega, by omega⟩
    | true => simp [tick, copy_value, exponent]

theorem tick_none {bits : List Bool} (h : (tick bits).value = none) : exponent bits = 0 := by
  simpa only [h] using tick_spec bits

theorem tick_some {bits rest : List Bool} (h : (tick bits).value = some rest) :
    rest.length = bits.length ∧ exponent bits = exponent rest + 1 := by
  simpa only [h] using tick_spec bits

theorem exponent_natBits (w n : Nat) (hn : n < 2^w) : exponent (natBits w n) = n := by
  simpa only [natBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] using
    WordCircuit.exponent_word (BitVec.ofNat w n)

def run {m : Type → Type} [Monad m]
    (step : Address → Store → m (Run HeapExpression.Result))
    (bits : List Bool) (acc : Address) (store : Store) : m (Run HeapExpression.Result) :=
  let next := tick bits
  match h : next.value with
  | none =>
    let out := HeapBits.copy acc
    pure ⟨some (out.value, store), next.steps + out.steps + 1⟩
  | some rest => do
    let body ← step acc store
    match body.value with
    | none => pure ⟨none, next.steps + body.steps + 1⟩
    | some (root, store) =>
      let out ← run step rest root store
      pure ⟨out.value, next.steps + body.steps + out.steps + 2⟩
termination_by exponent bits
decreasing_by have hdec := (tick_some h).2; omega

def advance {m : Type → Type} [Monad m]
    (step : Address → Store → m (Run HeapExpression.Result)) : HeapExpression.Result → m HeapExpression.Result
  | none => pure none
  | some (root, store) => Run.value <$> step root store

private theorem repeat_none {m : Type → Type} [Monad m] [LawfulMonad m]
    (step : Address → Store → m (Run HeapExpression.Result)) (n : Nat) :
    repeatDenote (advance step) n none = pure none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatDenote, advance, ih]

/-- Exact monadic behavior, not just equality in distribution: all body effects
and adaptive continuations agree with the source-counted iteration. -/
theorem run_erase {m : Type → Type} [Monad m] [LawfulMonad m]
    (step : Address → Store → m (Run HeapExpression.Result))
    (bits : List Bool) (acc : Address) (store : Store) :
    Run.value <$> run step bits acc store =
      repeatDenote (advance step) (exponent bits) (some (acc, store)) := by
  generalize hn : exponent bits = n
  induction n generalizing bits acc store with
  | zero =>
    rw [run]
    dsimp only
    split
    · simp [copy_value, repeatDenote]
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
      have h := (tick_some ht).2
      have hn' : exponent rest = n := by omega
      simp only [map_bind, repeatDenote, advance, bind_map_left]
      congr 1
      funext body
      cases hv : body.value with
      | none => simp [repeat_none]
      | some p =>
        rcases p with ⟨root, next⟩
        simpa only [hv, map_bind, map_pure, bind_pure_comp, Functor.map_map, Function.comp_def] using
          ih rest root next hn'

open OracleComp in
/-- A bound on every adaptive reply path, including state-changing bodies and
early failure. The body invariant supplies the maximum returned-address size. -/
theorem run_costed {I S : Type} {spec : OracleSpec I}
    (step : Address → Store → StateT S (OracleComp spec) (Run HeapExpression.Result))
    (Inv : Address → Store → S → Prop) (nodes bodyCost : Nat)
    (haddr : ∀ root store state, Inv root store state → root.length ≤ nodes)
    (hstep : ∀ root store state, Inv root store state →
      ∀ z ∈ support ((step root store).run state), z.1.steps ≤ bodyCost ∧
        ∀ out heap, z.1.value = some (out, heap) → Inv out heap z.2)
    (bits : List Bool) (acc : Address) (store : Store) (state : S) (hi : Inv acc store state)
    (z : Run HeapExpression.Result × S) (hz : z ∈ support ((run step bits acc store).run state)) :
    z.1.steps ≤ exponent bits * (bodyCost + 2*bits.length + 3) + 2*bits.length + 2*nodes + 3 ∧
      ∀ out heap, z.1.value = some (out, heap) → Inv out heap z.2 := by
  generalize hn : exponent bits = n
  induction n generalizing bits acc store state z with
  | zero =>
    rw [run] at hz
    dsimp only at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, copy_value] at hz
      subst z
      have ha := haddr acc store state hi
      constructor
      · simp only [tick_steps, copy_steps, Nat.zero_mul]; omega
      · intro out heap he
        obtain ⟨rfl, rfl⟩ := Option.some.inj he
        exact hi
    · rename_i rest ht
      have h := (tick_some ht).2
      omega
  | succ n ih =>
    rw [run] at hz
    dsimp only at hz
    split at hz
    · rename_i ht
      have h := tick_none ht
      omega
    · rename_i rest ht
      have hrest := tick_some ht
      have hn' : exponent rest = n := by omega
      simp only [StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨⟨body, nextState⟩, hbody, hz⟩ := hz
      obtain ⟨hcost, hinv⟩ := hstep acc store state hi (body, nextState) hbody
      cases hv : body.value with
      | none =>
        simp only [hv, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst z
        constructor
        · simp only [tick_steps]; nlinarith
        · simp
      | some p =>
        rcases p with ⟨root, heap⟩
        simp only [hv, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨⟨out, finalState⟩, hout, rfl⟩ := hz
        obtain ⟨hbound, hfinal⟩ := ih rest root heap nextState (hinv root heap hv)
          (out, finalState) hout hn'
        constructor
        · simp only [tick_steps]
          rw [hrest.1] at hbound
          dsimp only at hcost hbound
          nlinarith
        · exact hfinal

end Signatures.Runtime.HeapLoop
