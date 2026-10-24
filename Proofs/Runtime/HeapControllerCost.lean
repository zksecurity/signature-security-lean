import Proofs.Runtime.HeapExpressionRefinement

/-! Polynomial envelopes for the bit-tape controller. `nodes` bounds the heap
throughout a run, not just at entry. The fold theorem derives preservation of
that bound from the source budget and the body's allocation refinement. -/

namespace Signatures.Runtime.HeapExpression

open HeapBits SharedHeap

def tapeBudget (cap nodes : Nat) : Nat := nodes * (2*cap + 2*nodes + 4)

def readBudget (cap nodes : Nat) : Nat := 3*tapeBudget cap nodes + 7*(nodes+1)

def allocBudget (cap nodes : Nat) : Nat :=
  2*tapeBudget cap nodes + 4*(2*cap + 2*nodes + 4) + 2*nodes + 8

def frameBudget (registers nodes : Nat) : Nat :=
  4*nodes + 2*registers*(nodes+1) + 6

theorem tape_le_budget {cap nodes : Nat} {heap : List Node}
    (hw : WellFormed cap heap) (hn : heap.length ≤ nodes) :
    (tape heap).length ≤ tapeBudget cap nodes := by
  apply (tape_length heap hw).trans
  dsimp [tapeBudget]
  gcongr

theorem read_le_budget {cap nodes : Nat} {heap : List Node}
    (hw : WellFormed cap heap) (hn : heap.length ≤ nodes)
    (store : Store) (hs : store.Represents heap) (root : Address) :
    (read root store.memory).steps ≤ readBudget cap nodes := by
  rw [hs.2]
  have h := read_steps heap root
  have ht := tape_le_budget hw hn
  dsimp [readBudget]
  omega

theorem alloc_le_budget {cap nodes : Nat} {heap : List Node}
    (hw : WellFormed cap heap) (hn : heap.length ≤ nodes)
    (store : Store) (hs : store.Represents heap) (node : Node)
    (hb : NodeBound cap heap.length node) :
    (alloc store node).steps ≤ allocBudget cap nodes := by
  have h := alloc_steps store node
  have ht := tape_le_budget hw hn
  have hb := node_bits_length node hb
  simp only [hs.1, hs.2] at h
  dsimp [allocBudget]
  omega

theorem framePush_le_budget {registers nodes : Nat} (roots : List Address) (root : Address)
    (hr : ∀ r ∈ roots, r.length < nodes) (hn : root.length < nodes)
    (hg : roots.length ≤ registers) :
    (framePush root (frameBits roots)).steps ≤ frameBudget registers nodes := by
  rw [framePush_steps]
  have hf := frameBits_length roots nodes hr
  have hm : roots.length*(nodes+1) ≤ registers*(nodes+1) := Nat.mul_le_mul_right _ hg
  dsimp [frameBudget]
  nlinarith

def primitiveBudget {a b : Ty CryptoAtom} (w nodes : Nat) (op : CryptoOp a b) : Nat :=
  let m := (FixedPorts.inputLayout op).width w
  let n := 1 + m + CryptoCircuit.gates w op
  let k := CryptoCircuit.outputWidth w op
  let size := tapeBudget (3*w+1) nodes
  3*(3*size + 7*(nodes+1) + 2*m + 5) +
    (n*(4*n+m+10) + k*(n+4) + 3) + 2*size + 4*(3+2*k) + 2*nodes + 10

theorem primitive_le_budget {r p₁ p₂ w nodes : Nat}
    [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
    {W₁ : WeierstrassCurve.Affine (ZMod p₁)} {W₂ : WeierstrassCurve.Affine (ZMod p₂)}
    {K M : Type} (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
    (encodeK : K → BitVec w) (encodeM : M → BitVec w)
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    {heap : List Node} (hw : WellFormed (3*w+1) heap) (hn : heap.length ≤ nodes)
    {a b : Ty CryptoAtom} (op : CryptoOp a b) (store : Store) (hs : store.Represents heap)
    (root : Address) (x : a.Value (cryptoBase (ZMod r) H₁ H₂ K M))
    (hx : Represents w (atomRep H₁ H₂ encodeK encodeM) heap a root x) :
    (runPrimitive (FixedPorts.inputLayout op) (CryptoCircuit.precompile w r W₁ W₂ op)
      store root).steps ≤ primitiveBudget w nodes op := by
  apply (runPrimitive_steps H₁ H₂ encodeK encodeM hr h₁ h₂ op store hs root x hx).trans
  have ht := tape_le_budget hw hn
  dsimp only [primitiveBudget]
  gcongr

/-- A syntax-computed multiplier. The maximum covers either branch, while the
source budget counts only the branch and fold iterations actually executed.
Its parameters are word width and a global node bound, not unfolded value size. -/
def budget (w nodes : Nat) {Γ : List (Ty CryptoAtom)} {a : Ty CryptoAtom} :
    Expr CryptoOp Γ a → Nat
  | .var _ => 3*nodes+6
  | .unit | .bool _ | .nat _ | .nil => allocBudget (3*w+1) nodes + 1
  | .pair l r | .cons l r => max (max (budget w nodes l) (budget w nodes r))
      (allocBudget (3*w+1) nodes + 3)
  | .fst x | .snd x => max (budget w nodes x) (readBudget (3*w+1) nodes + 4)
  | .branch c yes no => max (max (budget w nodes c)
      (max (budget w nodes yes) (budget w nodes no))) (readBudget (3*w+1) nodes + 4)
  | .letE x body => max (max (budget w nodes x) (budget w nodes body))
      (frameBudget Γ.length nodes + 2)
  | .op op x => max (budget w nodes x) (primitiveBudget w nodes op + 1)
  | .fold xs init body => max (max (budget w nodes xs)
      (max (budget w nodes init) (budget w nodes body)))
      (readBudget (3*w+1) nodes + 2*nodes + 2*frameBudget (Γ.length+1) nodes + 10)

variable {Atom : Type} {base : Atom → Type} {w cap : Nat}
  {leaf : (a : Atom) → List Bool → base a → Prop}

theorem bind_steps_spec {heap : List Node} {a : Ty Atom} {x : a.Value base}
    {allocations firstCost nextCost : Nat} {first : Run Result}
    {next : Address × Store → Run Result}
    (hfirst : ResultSpec w cap leaf heap allocations x first) (hf : first.steps ≤ firstCost)
    (hnext : ∀ extra root store, first.value = some (root, store) →
      store.Represents (heap ++ extra) → WellFormed cap (heap ++ extra) →
      Represents w leaf (heap ++ extra) a root x → extra.length ≤ allocations →
      (next (root, store)).steps ≤ nextCost) :
    (bind first next).steps ≤ firstCost + nextCost + 1 := by
  obtain ⟨extra, root, store, hv, hs, hw, hx, hn⟩ := hfirst
  have ht := hnext extra root store hv hs hw hx hn
  simp only [bind, hv]
  omega

/-- The body may allocate and change the accumulator. Its cost includes a
per-iteration overhead (e.g. copying the two fold registers). All other scans,
termination tests, and the final returned-address copy are charged here. -/
theorem foldLoop_steps {a b : Ty Atom} (Inv : List Node → Prop)
    (hInv : ∀ heap extra, Inv heap → Inv (heap ++ extra))
    (source : a.Value base → b.Value base → Run (b.Value base))
    (check : a.Value base → b.Value base → Prop)
    (step : Address → Address → Store → Run Result) (nodes factor overhead : Nat)
    (hfactor : readBudget cap nodes + 2*nodes + overhead + 3 ≤ factor)
    (hstep : ∀ heap head acc store (x : a.Value base) (y : b.Value base),
      Inv heap → store.Represents heap → WellFormed cap heap →
      Represents w leaf heap a head x → Represents w leaf heap b acc y → check x y →
      heap.length + (source x y).steps ≤ nodes →
      ResultSpec w cap leaf heap (source x y).steps (source x y).value (step head acc store) ∧
        (step head acc store).steps ≤ (source x y).steps*factor + overhead)
    (heap : List Node) (root acc : Address) (store : Store) (fuel : Address)
    (xs : List (a.Value base)) (y : b.Value base)
    (hi : Inv heap) (hs : store.Represents heap) (hw : WellFormed cap heap)
    (hx : Represents w leaf heap (.list a) root xs) (hy : Represents w leaf heap b acc y)
    (hf : xs.length < fuel.length) (hc : NaturalRange.foldChecks check source xs y)
    (hn : heap.length + (foldRun source xs y).steps ≤ nodes) :
    (foldLoop step fuel root acc store).steps ≤ (foldRun source xs y).steps*factor := by
  induction xs generalizing heap root acc store fuel y with
  | nil =>
    cases fuel with
    | nil => simp at hf
    | cons u fuel =>
      have hr := read_le_budget (nodes := nodes) hw (by omega) store hs root
      have ha := hy.address_lt
      cases hx with
      | nil h =>
        simp only [foldLoop, hs.2, read_value, h, copy_steps, foldRun, Nat.one_mul]
        rw [hs.2] at hr
        simp only [foldRun] at hn
        omega
  | cons x xs ih =>
    cases fuel with
    | nil => simp at hf
    | cons u fuel =>
      have hr := read_le_budget (nodes := nodes) hw (by omega) store hs root
      cases hx with
      | cons h hhead htail =>
        rename_i head tail
        have hn' : heap.length + (source x y).steps ≤ nodes := by
          simp only [foldRun] at hn
          omega
        obtain ⟨hb, hbsteps⟩ := hstep heap head acc store x y hi hs hw hhead hy hc.1 hn'
        obtain ⟨extra, next, nextStore, hv, hstore, hwell, hvalue, hlen⟩ := hb
        have hrest := ih (heap ++ extra) tail next nextStore fuel (source x y).value
          (hInv heap extra hi) hstore hwell (htail.append extra) hvalue
          (by simpa using hf) hc.2 (by
            simp only [List.length_append, foldRun] at *
            omega)
        simp only [foldLoop, hs.2, read_value, h, bind, hv, foldRun]
        rw [hs.2] at hr
        nlinarith

end Signatures.Runtime.HeapExpression
