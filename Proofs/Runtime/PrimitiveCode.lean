import Proofs.Runtime.FixedPorts
import Proofs.Runtime.CryptoCircuitExecution

/-! Precompiled, assignment-independent bit programs for all arithmetic
instructions. Correctness and cell bounds refer to the same executable code.
The caller supplies operand bits; heap access and uniform compilation time
are separate obligations, not hidden in the online bound. -/

namespace Signatures.Runtime.CryptoCircuit

open Std.Sat CircuitWires FixedPorts WeierstrassCurve

variable {r p₁ p₂ w : Nat} [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)} {K M : Type}

/-- No input value or runtime bit appears among the compiler's arguments. -/
def precompile (w r : Nat) (W₁ : Affine (ZMod p₁)) (W₂ : Affine (ZMod p₂))
    {a b : Ty CryptoAtom} (op : CryptoOp a b) : CircuitExecution.Code :=
  let ports := (inputLayout op).ports w
  let out := compile r W₁ W₂ ports.graph op ports.refs
  CircuitExecution.lower out.graph (outputs out.refs)

omit [Fact p₁.Prime] [Fact p₂.Prime] in
theorem precompile_length (w r : Nat) (W₁ : Affine (ZMod p₁)) (W₂ : Affine (ZMod p₂))
    {a b : Ty CryptoAtom} (op : CryptoOp a b) (input : List Bool) :
    ((precompile w r W₁ W₂ op).run input).value.length = outputWidth w op := by
  rw [CircuitExecution.Code.run_length]
  simp only [precompile, CircuitExecution.lower, List.length_map]
  exact outputs_length _ op _

theorem precompile_steps (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (W₁ : Affine (ZMod p₁)) (W₂ : Affine (ZMod p₂))
    {a b : Ty CryptoAtom} (op : CryptoOp a b) (input : Vector Bool ((inputLayout op).width w)) :
    let m := (inputLayout op).width w
    let n := 1 + m + gates w op
    ((precompile w r W₁ W₂ op).run input.toList).steps ≤
      n*(4*n + m + 10) + outputWidth w op*(n + 4) + 3 := by
  simpa only [execute, precompile, CircuitExecution.lower_run, Layout.ports_size] using
    execute_steps hr h₁ h₂ W₁ W₂ ((inputLayout op).ports w).graph op
      ((inputLayout op).ports w).refs input

theorem precompile_cells (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (W₁ : Affine (ZMod p₁)) (W₂ : Affine (ZMod p₂)) {a b : Ty CryptoAtom} (op : CryptoOp a b) :
    let m := (inputLayout op).width w
    let n := 1 + m + gates w op
    (precompile w r W₁ W₂ op).cells ≤ n*(2*n + m + 4) + outputWidth w op*(n + 2) + 2 := by
  let ports := (inputLayout op).ports w
  let out := compile r W₁ W₂ ports.graph op ports.refs
  have hs := compile_size hr h₁ h₂ W₁ W₂ ports.graph op ports.refs
  have hc := CircuitExecution.lower_cells out.graph (outputs out.refs)
  have hl := outputs_length out.graph op out.refs
  change out.graph.decls.size ≤ ports.graph.decls.size + gates w op at hs
  rw [show ports.graph.decls.size = 1 + (inputLayout op).width w from
    Layout.ports_size _ _] at hs
  rw [hl] at hc
  change (CircuitExecution.lower out.graph (outputs out.refs)).cells ≤ _
  exact hc.trans (by gcongr)

variable (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
  (encodeK : K → BitVec w) (encodeM : M → BitVec w)
  [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂]

/-- The input relation is a specification of existing operand bits, not a
request to compute an abstract group encoding during online execution. -/
theorem precompile_correct
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts) {a b : Ty CryptoAtom} (op : CryptoOp a b)
    (input : Vector Bool ((inputLayout op).width w))
    (x : a.Value (cryptoBase (ZMod r) H₁ H₂ K M))
    (hb : NaturalRange.ValueBound w x)
    (hx : ∀ i, input[i] = (inputLayout op).encode H₁ H₂ encodeK encodeM x i)
    (hs : Safe (w := w) H₁ H₂ op x) :
    ((precompile w r W₁ W₂ op).run input.toList).value = portBits H₁ H₂ encodeK encodeM
      ((arithmetic (ZMod r) H₁ H₂ K M cost).execute op x) := by
  exact execute_correct H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm cost
    ((inputLayout op).ports w).graph op ((inputLayout op).ports w).refs input x
    ((inputLayout op).ports_correct H₁ H₂ encodeK encodeM input x hb hx) hs

end Signatures.Runtime.CryptoCircuit
