import Signatures.Runtime.HeapExpression

/-! Refinement invariants for expression execution. The allocation budget counts
new shared nodes, not bit steps; bit costs remain the runner's explicit counters.
This invariant is preserved through sequencing and the fuelled list controller. -/

namespace Signatures.Runtime.HeapExpression

open HeapBits SharedHeap

variable {Atom : Type} {base : Atom → Type} {w cap : Nat}
  {leaf : (a : Atom) → List Bool → base a → Prop}

def ResultSpec (w cap : Nat) (leaf : (a : Atom) → List Bool → base a → Prop)
    (heap : List Node) (allocations : Nat) {t : Ty Atom} (value : t.Value base) (r : Run Result) : Prop :=
  ∃ extra root store, r.value = some (root, store) ∧ store.Represents (heap ++ extra) ∧
    WellFormed cap (heap ++ extra) ∧ Represents w leaf (heap ++ extra) t root value ∧
    extra.length ≤ allocations

theorem ResultSpec.mono {heap : List Node} {a b : Nat} {t : Ty Atom} {x : t.Value base} {r : Run Result}
    (h : ResultSpec w cap leaf heap a x r) (hab : a ≤ b) : ResultSpec w cap leaf heap b x r := by
  obtain ⟨extra, root, store, hv, hs, hw, hx, hn⟩ := h
  exact ⟨extra, root, store, hv, hs, hw, hx, hn.trans hab⟩

theorem ResultSpec.of_value_eq {heap : List Node} {n : Nat} {t : Ty Atom} {x : t.Value base}
    {r s : Run Result} (h : ResultSpec w cap leaf heap n x r) (he : s.value = r.value) :
    ResultSpec w cap leaf heap n x s := by
  obtain ⟨extra, root, store, hv, hs, hw, hx, hn⟩ := h
  exact ⟨extra, root, store, he.trans hv, hs, hw, hx, hn⟩

theorem ResultSpec.rebase {heap added : List Node} {n : Nat} {t : Ty Atom} {x : t.Value base}
    {r : Run Result} (h : ResultSpec w cap leaf (heap ++ added) n x r) :
    ResultSpec w cap leaf heap (added.length+n) x r := by
  obtain ⟨extra, root, store, hv, hs, hw, hx, hn⟩ := h
  refine ⟨added ++ extra, root, store, hv, ?_, ?_, ?_, by simp; omega⟩
  · simpa only [List.append_assoc] using hs
  · simpa only [List.append_assoc] using hw
  · simpa only [List.append_assoc] using hx

theorem bind_spec {heap : List Node} {a b : Ty Atom} {x : a.Value base} {y : b.Value base}
    {n m : Nat} {first : Run Result} {next : Address × Store → Run Result}
    (hfirst : ResultSpec w cap leaf heap n x first)
    (hnext : ∀ extra root store, first.value = some (root, store) →
      store.Represents (heap ++ extra) → WellFormed cap (heap ++ extra) →
      Represents w leaf (heap ++ extra) a root x → extra.length ≤ n →
      ResultSpec w cap leaf (heap ++ extra) m y (next (root, store))) :
    ResultSpec w cap leaf heap (n+m) y (bind first next) := by
  obtain ⟨extra, root, store, hv, hs, hw, hx, hn⟩ := hfirst
  have h := (hnext extra root store hv hs hw hx hn).rebase
  exact (h.mono (by omega)).of_value_eq (by simp only [bind, hv])

theorem alloc_spec {heap : List Node} (store : Store) (hs : store.Represents heap)
    (hw : WellFormed cap heap) (node : Node) (hn : NodeBound cap heap.length node)
    {t : Ty Atom} (x : t.Value base)
    (hx : Represents w leaf (heap ++ [node]) t (alloc store node).value.1 x) :
    ResultSpec w cap leaf heap 1 x (lift (alloc store node)) := by
  exact ⟨[node], _, _, rfl, alloc_represents store heap hs node,
    wellFormed_append heap node hw (by simpa only [Nat.zero_add] using hn), hx, le_rfl⟩

theorem root_spec {heap : List Node} (store : Store) (hs : store.Represents heap)
    (hw : WellFormed cap heap) {t : Ty Atom} {root : Address} {x : t.Value base}
    (hx : Represents w leaf heap t root x) (r : Run Result) (hr : r.value = some (root, store)) :
    ResultSpec w cap leaf heap 0 x r := by
  exact ⟨[], root, store, hr, by simpa using hs, by simpa using hw, by simpa using hx, le_rfl⟩

theorem ResultSpec.memory_bound {heap : List Node} {n : Nat} {t : Ty Atom} {x : t.Value base}
    {r : Run Result} (h : ResultSpec w cap leaf heap n x r) (root : Address) (store : Store)
    (hv : r.value = some (root, store)) :
    store.memory.length ≤ (heap.length+n)*(2*cap + 2*(heap.length+n) + 4) := by
  obtain ⟨extra, addr, next, he, hs, hw, _, hn⟩ := h
  have hsame := Option.some.inj (he.symm.trans hv)
  have hstore : next = store := congrArg Prod.snd hsame
  subst next
  rw [hs.2]
  apply (tape_length _ hw).trans
  simp only [List.length_append]
  gcongr

/-- Every well-typed list iteration consumes one fuel cell, while the body may
append to the heap. Old list tails and the caller's invariant survive those appends. -/
theorem foldLoop_spec {a b : Ty Atom} (Inv : List Node → Prop)
    (hInv : ∀ heap extra, Inv heap → Inv (heap ++ extra))
    (source : a.Value base → b.Value base → Run (b.Value base))
    (check : a.Value base → b.Value base → Prop)
    (step : Address → Address → Store → Run Result)
    (hstep : ∀ heap head acc store (x : a.Value base) (y : b.Value base),
      Inv heap → store.Represents heap → WellFormed cap heap →
      Represents w leaf heap a head x → Represents w leaf heap b acc y → check x y →
      ResultSpec w cap leaf heap (source x y).steps (source x y).value (step head acc store))
    (heap : List Node) (root acc : Address) (store : Store) (fuel : Address)
    (xs : List (a.Value base)) (y : b.Value base)
    (hi : Inv heap) (hs : store.Represents heap) (hw : WellFormed cap heap)
    (hx : Represents w leaf heap (.list a) root xs) (hy : Represents w leaf heap b acc y)
    (hf : xs.length < fuel.length) (hc : NaturalRange.foldChecks check source xs y) :
    ResultSpec w cap leaf heap (foldRun source xs y).steps (foldRun source xs y).value
      (foldLoop step fuel root acc store) := by
  induction xs generalizing heap root acc store fuel y with
  | nil =>
    cases fuel with
    | nil => simp at hf
    | cons u fuel =>
      cases hx with
      | nil h =>
        refine ⟨[], acc, store, ?_, ?_, ?_, ?_, by simp⟩
        · simp [foldLoop, hs.2, read_value, h, copy_value]
        · simpa using hs
        · simpa using hw
        · simpa [foldRun] using hy
  | cons x xs ih =>
    cases fuel with
    | nil => simp at hf
    | cons u fuel =>
      cases hx with
      | cons h hhead htail =>
        rename_i head tail
        have hb := hstep heap head acc store x y hi hs hw hhead hy hc.1
        have hr : ResultSpec w cap leaf heap
            ((source x y).steps + (foldRun source xs (source x y).value).steps)
            (foldRun source xs (source x y).value).value
            (bind (step head acc store) (fun p => foldLoop step fuel tail p.1 p.2)) := by
          apply bind_spec hb
          intro extra next nextStore _ hstore hwell hvalue _
          exact ih (heap ++ extra) tail next nextStore fuel (source x y).value
            (hInv heap extra hi) hstore hwell (htail.append extra) hvalue
            (by simpa using hf) hc.2
        have hr' := hr.mono (show _ ≤ (foldRun source (x::xs) y).steps by simp [foldRun])
        apply hr'.of_value_eq
        simp only [foldLoop, hs.2, read_value, h]

end Signatures.Runtime.HeapExpression
