import Proofs.Runtime.HeapExpressionCost
import Proofs.Runtime.ProgramRange

/-! Procedure argument frames on the shared bit heap. Arguments all read the
caller's frame; their results form a fresh, explicitly copied callee frame.
Heap growth preserves roots of earlier arguments without copying their values. -/

namespace Signatures.Runtime.HeapArguments

open HeapBits SharedHeap HeapExpression WeierstrassCurve

def run : List Code → List Bool → Store → Run (Option (List Bool × Store))
  | [], _, store => ⟨some ([], store), 1⟩
  | head :: tail, frame, store =>
    HeapExpression.bind (head.run frame store) fun p =>
      HeapExpression.bind (run tail frame p.2) fun q =>
        let out := framePush p.1 q.1
        ⟨some (out.value, q.2), out.steps + 1⟩

def compile {p₁ p₂ : Nat} (w r : Nat) (W₁ : Affine (ZMod p₁)) (W₂ : Affine (ZMod p₂))
    {Γ Δ : List (Ty CryptoAtom)} : Args CryptoOp Γ Δ → List Code
  | .nil => []
  | .cons head tail => HeapExpression.compile w r W₁ W₂ head :: compile w r W₁ W₂ tail

def budget (w nodes : Nat) {Γ Δ : List (Ty CryptoAtom)} : Args CryptoOp Γ Δ → Nat
  | .nil => 1
  | .cons (Δ := rest) head tail => max (max (HeapExpression.budget w nodes head) (budget w nodes tail))
      (frameBudget rest.length nodes + 3)

def ResultSpec {Atom : Type} {base : Atom → Type} (w cap : Nat)
    (leaf : (a : Atom) → List Bool → base a → Prop)
    (heap : List Node) (allocations : Nat) {Δ : List (Ty Atom)} (env : Env base Δ)
    (r : Run (Option (List Bool × Store))) : Prop :=
  ∃ extra roots store, r.value = some (frameBits roots, store) ∧
    store.Represents (heap ++ extra) ∧ WellFormed cap (heap ++ extra) ∧
    EnvRep w leaf (heap ++ extra) roots env ∧ extra.length ≤ allocations

variable {r p₁ p₂ w : Nat} [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)} {K M : Type}
  (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
  (encodeK : K → BitVec w) (encodeM : M → BitVec w)
  [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂]

theorem compile_costed
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts) {Γ Δ : List (Ty CryptoAtom)} (args : Args CryptoOp Γ Δ)
    (heap : List Node) (roots : List Address)
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) (store : Store)
    (hs : store.Represents heap) (hw : WellFormed (3*w+1) heap)
    (he : EnvRep w (atomRep H₁ H₂ encodeK encodeM) heap roots env)
    (ht : NaturalRange.ArgsBound cost w args env) (nodes factor : Nat)
    (hn : heap.length + (args.run (arithmetic (ZMod r) H₁ H₂ K M cost) env).steps ≤ nodes)
    (hb : budget w nodes args ≤ factor) :
    let source := args.run (arithmetic (ZMod r) H₁ H₂ K M cost) env
    let actual := run (compile w r W₁ W₂ args) (frameBits roots) store
    ResultSpec w (3*w+1) (atomRep H₁ H₂ encodeK encodeM) heap source.steps source.value actual ∧
      actual.steps ≤ source.steps * factor := by
  let P := arithmetic (ZMod r) H₁ H₂ K M cost
  let L := atomRep (r := r) H₁ H₂ encodeK encodeM
  change ResultSpec w (3*w+1) L heap (args.run P env).steps (args.run P env).value _ ∧
    (run (compile w r W₁ W₂ args) (frameBits roots) store).steps ≤ (args.run P env).steps*factor
  change heap.length + (args.run P env).steps ≤ nodes at hn
  induction args generalizing heap roots store with
  | nil =>
    refine ⟨⟨[], [], store, rfl, ?_, ?_, .nil, by simp [Args.run]⟩, ?_⟩
    · simpa using hs
    · simpa using hw
    · simpa only [budget, compile, run, Args.run, Nat.one_mul] using hb
  | @cons t Δ head tail ih =>
    simp only [budget, max_le_iff] at hb
    simp only [Args.run] at hn
    have hhead := HeapExpression.compile_spec H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm
      cost head heap roots env store hs hw he ht.1
    change HeapExpression.ResultSpec w (3*w+1) L heap (head.run P env).steps (head.run P env).value _ at hhead
    have hcost := HeapExpression.compile_steps H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm
      cost head heap roots env store hs hw he ht.1 nodes factor
      (by change heap.length + (head.run P env).steps ≤ nodes; omega) hb.1.1
    change _ ≤ (head.run P env).steps*factor at hcost
    obtain ⟨extra, root, next, hv, hs₁, hw₁, hx, hlen⟩ := hhead
    obtain ⟨htail, htailCost⟩ := ih (heap ++ extra) roots next hs₁ hw₁ (he.append extra) ht.2
      hb.1.2 (by simp only [List.length_append]; omega)
    obtain ⟨more, output, finalStore, htval, hs₂, hw₂, hout, hmore⟩ := htail
    have hx' := hx.append more
    have hsize : ((heap ++ extra) ++ more).length ≤ nodes := by
      simp only [List.length_append]; omega
    have hpush := framePush_le_budget output root
      (fun addr h => (hout.addresses addr h).trans_le hsize)
      (hx'.address_lt.trans_le hsize) (le_of_eq hout.length)
    constructor
    · refine ⟨extra ++ more, root :: output, finalStore, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [compile, run, HeapExpression.bind, hv, htval, framePush_value]
      · simpa only [List.append_assoc] using hs₂
      · simpa only [List.append_assoc] using hw₂
      · simpa only [List.append_assoc, Args.run] using EnvRep.cons hx' hout
      · simp only [List.length_append, Args.run]; omega
    · simp only [compile, run, HeapExpression.bind, hv, htval, Args.run]
      nlinarith [hb.2]

/-- Only the initial range and total source budget are needed; all argument
intermediate widths follow from the source trace theorem. -/
theorem compile_costed_of_budget
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts) {Γ Δ : List (Ty CryptoAtom)} (args : Args CryptoOp Γ Δ)
    (heap : List Node) (roots : List Address)
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) (store : Store)
    (hs : store.Represents heap) (hw : WellFormed (3*w+1) heap)
    (he : EnvRep w (atomRep H₁ H₂ encodeK encodeM) heap roots env)
    (bits : Nat) (hebits : NaturalRange.EnvBound bits env)
    (hb : bits + (args.run (arithmetic (ZMod r) H₁ H₂ K M cost) env).steps ≤ w) :
    let source := args.run (arithmetic (ZMod r) H₁ H₂ K M cost) env
    let actual := run (compile w r W₁ W₂ args) (frameBits roots) store
    ResultSpec w (3*w+1) (atomRep H₁ H₂ encodeK encodeM) heap source.steps source.value actual ∧
      actual.steps ≤ source.steps * budget w (heap.length + source.steps) args :=
  compile_costed H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm cost args heap roots env store hs hw he
    (NaturalRange.args_trace_bound cost args bits w env hebits hb) _ _ le_rfl le_rfl

end Signatures.Runtime.HeapArguments
