import Proofs.Runtime.HeapPorts
import Proofs.Runtime.PrimitiveCode

/-! One primitive instruction executed on shared-heap roots. The online runner
loads bit operands, runs precompiled finite code, and allocates a word node.
Its refinement and cost include all three operations, not only gate evaluation. -/

namespace Signatures.Runtime.SharedHeap

open HeapBits FixedPorts WeierstrassCurve

def runPrimitive {a : Ty CryptoAtom} (layout : Layout a) (code : CircuitExecution.Code)
    (store : Store) (addr : Address) : Run (Option (Address × Store)) :=
  let input := loadPorts layout store.memory addr
  match input.value with
  | none => ⟨none, input.steps + 1⟩
  | some bits =>
    let output := code.run bits
    let result := alloc store (.word output.value)
    ⟨some result.value, input.steps + output.steps + result.steps + 2⟩

variable {r p₁ p₂ w : Nat} [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)} {K M : Type}
  (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
  (encodeK : K → BitVec w) (encodeM : M → BitVec w)
  [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂]

private theorem code_on_ports
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts) {a b : Ty CryptoAtom} (op : CryptoOp a b)
    (x : a.Value (cryptoBase (ZMod r) H₁ H₂ K M)) (hb : NaturalRange.ValueBound w x)
    (hs : CryptoCircuit.Safe (w := w) H₁ H₂ op x) :
    ((CryptoCircuit.precompile w r W₁ W₂ op).run (CryptoCircuit.portBits H₁ H₂ encodeK encodeM x)).value =
      CryptoCircuit.portBits H₁ H₂ encodeK encodeM ((arithmetic (ZMod r) H₁ H₂ K M cost).execute op x) := by
  simpa only [Vector.toList_ofFn, Layout.encode_bits] using
    CryptoCircuit.precompile_correct H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm cost op
      (Vector.ofFn ((inputLayout op).encode H₁ H₂ encodeK encodeM x)) x hb (by intro i; simp) hs

theorem runPrimitive_value
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts) {heap : List Node} {a b : Ty CryptoAtom} (op : CryptoOp a b)
    (store : Store) (hstore : store.Represents heap) (addr : Address)
    (x : a.Value (cryptoBase (ZMod r) H₁ H₂ K M))
    (hx : Represents w (atomRep H₁ H₂ encodeK encodeM) heap a addr x)
    (hs : CryptoCircuit.Safe (w := w) H₁ H₂ op x) :
    (runPrimitive (inputLayout op) (CryptoCircuit.precompile w r W₁ W₂ op) store addr).value =
      some (alloc store (.word (CryptoCircuit.portBits H₁ H₂ encodeK encodeM
        ((arithmetic (ZMod r) H₁ H₂ K M cost).execute op x)))).value := by
  have hi := loadPorts_value H₁ H₂ encodeK encodeM (inputLayout op) addr x hx
  have hc := code_on_ports H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm cost op x
    (represents_range H₁ H₂ encodeK encodeM hx) hs
  simp only [runPrimitive, hstore.2, hi, hc]

private theorem result_range (cost : PrimitiveCosts) {a b : Ty CryptoAtom} (op : CryptoOp a b)
    (x : a.Value (cryptoBase (ZMod r) H₁ H₂ K M)) (hx : NaturalRange.ValueBound w x)
    (hs : CryptoCircuit.Safe (w := w) H₁ H₂ op x) :
    NaturalRange.ValueBound w ((arithmetic (ZMod r) H₁ H₂ K M cost).execute op x) := by
  cases op with
  | natAdd => exact hs
  | natSub => exact (Nat.sub_le _ _).trans_lt hx.1
  | finVal n => exact hx
  | finZero n => exact Nat.two_pow_pos _
  | finOfNat n => exact (Nat.mod_le _ _).trans_lt hx
  | _ => trivial

/-- The allocated output has the source instruction's type and meaning.
All previously represented roots remain valid by `Represents.append`. -/
theorem primitive_result_represents
    (cost : PrimitiveCosts) {heap : List Node} {a b : Ty CryptoAtom} (op : CryptoOp a b)
    (store : Store) (hstore : store.Represents heap)
    (x : a.Value (cryptoBase (ZMod r) H₁ H₂ K M)) (hx : NaturalRange.ValueBound w x)
    (hs : CryptoCircuit.Safe (w := w) H₁ H₂ op x) :
    let y := (arithmetic (ZMod r) H₁ H₂ K M cost).execute op x
    let node := Node.word (CryptoCircuit.portBits H₁ H₂ encodeK encodeM y)
    Represents w (atomRep H₁ H₂ encodeK encodeM) (heap ++ [node]) b (alloc store node).value.1 y := by
  have hy := result_range H₁ H₂ cost op x hx hs
  have hl := alloc_lookup store heap hstore
    (.word (CryptoCircuit.portBits H₁ H₂ encodeK encodeM ((arithmetic (ZMod r) H₁ H₂ K M cost).execute op x)))
  cases op <;> first | exact .atom hl ⟨rfl, hy⟩ | exact .nat hl hy | exact .bool hl

omit [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂] in
theorem runPrimitive_steps
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    {heap : List Node} {a b : Ty CryptoAtom} (op : CryptoOp a b)
    (store : Store) (hstore : store.Represents heap) (addr : Address)
    (x : a.Value (cryptoBase (ZMod r) H₁ H₂ K M))
    (hx : Represents w (atomRep H₁ H₂ encodeK encodeM) heap a addr x) :
    let m := (inputLayout op).width w
    let n := 1 + m + CryptoCircuit.gates w op
    let k := CryptoCircuit.outputWidth w op
    let size := (tape heap).length
    (runPrimitive (inputLayout op) (CryptoCircuit.precompile w r W₁ W₂ op) store addr).steps ≤
      3*(3*size + 7*(heap.length+1) + 2*m + 5) +
      (n*(4*n+m+10) + k*(n+4) + 3) + 2*size + 4*(3+2*k) + 2*heap.length + 10 := by
  let code := CryptoCircuit.precompile w r W₁ W₂ op
  let bits := CryptoCircuit.portBits H₁ H₂ encodeK encodeM x
  have hi := loadPorts_value H₁ H₂ encodeK encodeM (inputLayout op) addr x hx
  have hs := loadPorts_steps H₁ H₂ encodeK encodeM (inputLayout op) addr x hx
  have hp := input_portNodes op
  have hc := CryptoCircuit.precompile_steps hr h₁ h₂ W₁ W₂ op
    (Vector.ofFn ((inputLayout op).encode H₁ H₂ encodeK encodeM x))
  simp only [Vector.toList_ofFn, Layout.encode_bits] at hc
  have ha := alloc_steps store (.word (code.run bits).value)
  have hl := CryptoCircuit.precompile_length w r W₁ W₂ op bits
  change (code.run bits).value.length = CryptoCircuit.outputWidth w op at hl
  simp only [Node.bits, List.length_cons, List.length_append, unary_length, hl,
    hstore.1, hstore.2] at ha
  simp only [runPrimitive, hstore.2, hi]
  dsimp only [code, bits] at ha
  nlinarith

omit [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂] in
theorem primitive_word_bound (w : Nat) {a b : Ty CryptoAtom} (op : CryptoOp a b) :
    CryptoCircuit.outputWidth w op ≤ 3*w + 1 := by
  cases op <;> simp [CryptoCircuit.outputWidth] <;> omega

omit [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂] in
theorem primitive_wellFormed (w r : Nat) (W₁ : Affine (ZMod p₁)) (W₂ : Affine (ZMod p₂))
    {heap : List Node} (hh : WellFormed (3*w+1) heap) {a b : Ty CryptoAtom} (op : CryptoOp a b)
    (input : List Bool) :
    WellFormed (3*w+1) (heap ++ [.word ((CryptoCircuit.precompile w r W₁ W₂ op).run input).value]) := by
  apply wellFormed_append heap _ hh
  change ((CryptoCircuit.precompile w r W₁ W₂ op).run input).value.length ≤ _
  rw [CryptoCircuit.precompile_length]
  exact primitive_word_bound w op

end Signatures.Runtime.SharedHeap
