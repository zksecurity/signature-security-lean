import Signatures.Runtime.SharedHeap

/-! Type-indexed meanings of shared heap roots. Atom encodings are supplied by
the primitive backend. Products and lists are linked nodes, never flattened
semantic values; natural words carry an explicit no-truncation condition. -/

namespace Signatures.Runtime.SharedHeap

open HeapBits

variable {Atom : Type} {base : Atom → Type}

def natBits (w n : Nat) : List Bool := List.ofFn (fun i : Fin w => (BitVec.ofNat w n).getLsbD i)

inductive Represents (w : Nat) (leaf : (a : Atom) → List Bool → base a → Prop) (heap : List Node) :
    (t : Ty Atom) → Address → t.Value base → Prop
  | atom {a addr bits x} : heap[addr.length]? = some (.word bits) → leaf a bits x →
      Represents w leaf heap (.atom a) addr x
  | unit {addr} : heap[addr.length]? = some (.word []) → Represents w leaf heap .unit addr ()
  | bool {addr x} : heap[addr.length]? = some (.word [x]) → Represents w leaf heap .bool addr x
  | nat {addr n} : heap[addr.length]? = some (.word (natBits w n)) → n < 2^w →
      Represents w leaf heap .nat addr n
  | pair {a b addr left right x y} : heap[addr.length]? = some (.pair left right) →
      Represents w leaf heap a left x → Represents w leaf heap b right y →
      Represents w leaf heap (.pair a b) addr (x, y)
  | nil {a addr} : heap[addr.length]? = some .nil → Represents w leaf heap (.list a) addr []
  | cons {a addr head tail x xs} : heap[addr.length]? = some (.cons head tail) →
      Represents w leaf heap a head x → Represents w leaf heap (.list a) tail xs →
      Represents w leaf heap (.list a) addr (x :: xs)

variable {w : Nat} {leaf : (a : Atom) → List Bool → base a → Prop}
  {heap : List Node} {t : Ty Atom} {addr : Address} {x : t.Value base}

theorem Represents.address_lt (h : Represents w leaf heap t addr x) : addr.length < heap.length := by
  cases h with
  | atom h _ | unit h | bool h | nat h _ | pair h _ _ | nil h | cons h _ _ =>
    exact (List.getElem?_eq_some_iff.mp h).choose

theorem Represents.pair_parts {a b : Ty Atom} {x : a.Value base × b.Value base}
    (h : Represents w leaf heap (.pair a b) addr x) :
    ∃ left right, heap[addr.length]? = some (.pair left right) ∧
      Represents w leaf heap a left x.1 ∧ Represents w leaf heap b right x.2 := by
  rcases x with ⟨x, y⟩
  cases h with
  | pair h hl hr => exact ⟨_, _, h, hl, hr⟩

theorem Represents.append (h : Represents w leaf heap t addr x) (extra : List Node) :
    Represents w leaf (heap ++ extra) t addr x := by
  have look {a : Address} {n : Node} (h : heap[a.length]? = some n) :
      (heap ++ extra)[a.length]? = some n := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).choose]
    exact h
  induction h with
  | atom h hl => exact .atom (look h) hl
  | unit h => exact .unit (look h)
  | bool h => exact .bool (look h)
  | nat h hn => exact .nat (look h) hn
  | pair h _ _ ihl ihr => exact .pair (look h) ihl ihr
  | nil h => exact .nil (look h)
  | cons h _ _ ihh iht => exact .cons (look h) ihh iht

/-- A backwards-linked list has fewer cons cells than the heap's node count.
This justifies a copied node counter as runtime fuel, without unfolding values. -/
theorem Represents.list_length {cap : Nat} {a : Ty Atom} {xs : List (a.Value base)}
    (hh : WellFormed cap heap) (hx : Represents w leaf heap (.list a) addr xs) :
    xs.length ≤ addr.length := by
  induction xs generalizing addr with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    cases hx with
    | cons h _ ht =>
      have hb := wellFormed_lookup hh h
      have hl := ih ht
      simp only [NodeBound] at hb
      simp only [List.length_cons]
      omega

theorem alloc_lookup (store : Store) (heap : List Node) (hs : store.Represents heap) (node : Node) :
    (heap ++ [node])[(alloc store node).value.1.length]? = some node := by
  rw [alloc_address, hs.1]
  simp

theorem alloc_pair {a b : Ty Atom} {left right : Address} {x : a.Value base} {y : b.Value base}
    (store : Store) (hs : store.Represents heap)
    (hx : Represents w leaf heap a left x) (hy : Represents w leaf heap b right y) :
    Represents w leaf (heap ++ [.pair left right]) (.pair a b)
      (alloc store (.pair left right)).value.1 (x, y) :=
  .pair (alloc_lookup store heap hs _) (hx.append _) (hy.append _)

theorem alloc_cons {a : Ty Atom} {head tail : Address} {x : a.Value base} {xs : List (a.Value base)}
    (store : Store) (hs : store.Represents heap)
    (hx : Represents w leaf heap a head x) (hxs : Represents w leaf heap (.list a) tail xs) :
    Represents w leaf (heap ++ [.cons head tail]) (.list a)
      (alloc store (.cons head tail)).value.1 (x :: xs) :=
  .cons (alloc_lookup store heap hs _) (hx.append _) (hxs.append _)

theorem pair_wellFormed {cap : Nat} {a b : Ty Atom} {left right : Address}
    {x : a.Value base} {y : b.Value base} (hh : WellFormed cap heap)
    (hx : Represents w leaf heap a left x) (hy : Represents w leaf heap b right y) :
    WellFormed cap (heap ++ [.pair left right]) := by
  apply wellFormed_append heap _ hh
  simpa only [Nat.zero_add, NodeBound] using And.intro hx.address_lt hy.address_lt

theorem cons_wellFormed {cap : Nat} {a : Ty Atom} {head tail : Address}
    {x : a.Value base} {xs : List (a.Value base)} (hh : WellFormed cap heap)
    (hx : Represents w leaf heap a head x) (hxs : Represents w leaf heap (.list a) tail xs) :
    WellFormed cap (heap ++ [.cons head tail]) := by
  apply wellFormed_append heap _ hh
  simpa only [Nat.zero_add, NodeBound] using And.intro hx.address_lt hxs.address_lt

end Signatures.Runtime.SharedHeap
