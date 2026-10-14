import Signatures.Runtime.CryptoCircuitCorrectness
import Signatures.Runtime.CircuitExecution

/-! End-to-end execution of one CryptoOp on represented input ports. The same
compiled circuit supplies both the arithmetic result and its cell-step bound.
This does not yet lower the surrounding source/replay program or its heap. -/

namespace Signatures.Runtime.CryptoCircuit

open Std.Sat CircuitWires WeierstrassCurve

variable {r p₁ p₂ w : Nat} [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)}
  {K M A : Type} [Hashable A] [DecidableEq A]

private def wordBits (x : BitVec w) : List Bool := List.ofFn (fun i : Fin w => x.getLsbD i)

/-- Fixed point encoding shared by circuit ports and external DLog challenges. -/
def pointBits {p : Nat} [Fact p.Prime] {W : Affine (ZMod p)} (P : W.Point) : List Bool :=
  wordBits (BitVec.ofNat w (EllipticCurveCode.encode P 0).val) ++
  wordBits (BitVec.ofNat w (EllipticCurveCode.encode P 1).val) ++
  wordBits (BitVec.ofNat w (EllipticCurveCode.encode P 2).val)

/-- Values on typed circuit ports, not a variable-length serialization format. -/
def portBits (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
    (encodeK : K → BitVec w) (encodeM : M → BitVec w) :
    {t : Ty CryptoAtom} → t.Value (cryptoBase (ZMod r) H₁ H₂ K M) → List Bool
  | .atom .scalar, x => wordBits (BitVec.ofNat w x.val)
  | .atom .point₁, x => pointBits (w := w) (x : W₁.Point)
  | .atom .point₂, x => pointBits (w := w) (x : W₂.Point)
  | .atom .key, x => wordBits (encodeK x)
  | .atom .message, x => wordBits (encodeM x)
  | .atom (.fin _), x => wordBits (BitVec.ofNat w x.val)
  | .unit, _ => []
  | .bool, x => [x]
  | .nat, x => wordBits (BitVec.ofNat w x)
  | .pair _ _, x => portBits H₁ H₂ encodeK encodeM x.1 ++ portBits H₁ H₂ encodeK encodeM x.2
  | .list _, xs => xs.flatMap (portBits H₁ H₂ encodeK encodeM)

omit [Fact r.Prime] in
theorem represented_outputs (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
    (encodeK : K → BitVec w) (encodeM : M → BitVec w) (assign : A → Bool) (aig : AIG A)
    {t : Ty CryptoAtom} (refs : Wires w aig t)
    (x : t.Value (cryptoBase (ZMod r) H₁ H₂ K M))
    (hx : Represents H₁ H₂ encodeK encodeM assign aig refs x) :
    (outputs refs).map (fun ref => AIG.denote assign ⟨aig, ref⟩) = portBits H₁ H₂ encodeK encodeM x := by
  have word (refs : AIG.RefVec aig w) (v : BitVec w)
      (h : PrimeFieldCircuit.Represents assign aig refs v) :
      (List.ofFn (fun i : Fin w => refs.get i i.isLt)).map
        (fun ref => AIG.denote assign ⟨aig, ref⟩) = wordBits v := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact h i i.isLt
  induction t with
  | atom a =>
    cases a with
    | scalar | key | message => exact word _ _ hx
    | fin n => exact word _ _ hx.2
    | point₁ | point₂ =>
      simp only [outputs, portBits, pointBits, List.map_append]
      rw [word _ _ (hx 0), word _ _ (hx 1), word _ _ (hx 2)]
  | unit => rfl
  | bool => exact congrArg List.singleton hx
  | nat => exact word _ _ hx.2
  | pair a b iha ihb =>
    simp only [outputs, portBits, List.map_append]
    rw [iha _ _ hx.1, ihb _ _ hx.2]
  | list a ih =>
    induction hx with
    | nil => rfl
    | cons hhead htail ihtail =>
      simp only [outputs, portBits, List.flatMap_cons, List.map_append]
      rw [ih _ _ hhead]
      exact congrArg (List.append _) ihtail

/-- Number of result bits. No CryptoOp returns a variable-length value. -/
def outputWidth {a b : Ty CryptoAtom} (w : Nat) : CryptoOp a b → Nat
  | .zero | .one | .add | .sub | .mul | .div | .neg | .natAdd | .natSub |
      .finVal _ | .finZero _ | .finOfNat _ => w
  | .zero₁ | .zero₂ | .add₁ | .add₂ | .sub₁ | .sub₂ | .scale₁ | .scale₂ => 3*w
  | .scalarEq | .point₁Eq | .point₂Eq | .keyEq | .messageEq | .natEq | .natLt => 1

theorem outputs_length (aig : AIG A) {a b : Ty CryptoAtom} (op : CryptoOp a b)
    (refs : Wires w aig b) : (outputs refs).length = outputWidth w op := by
  cases op <;> simp [outputs, outputWidth]
  all_goals first | rfl | omega

def execute {m : Nat} (r : Nat) (W₁ : Affine (ZMod p₁)) (W₂ : Affine (ZMod p₂))
    (aig : AIG (Fin m)) {a b : Ty CryptoAtom} (op : CryptoOp a b) (refs : Wires w aig a)
    (input : Vector Bool m) : Run (List Bool) :=
  let out := compile r W₁ W₂ aig op refs
  CircuitExecution.evaluate out.graph (outputs out.refs) input

theorem execute_steps {m : Nat} (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (W₁ : Affine (ZMod p₁)) (W₂ : Affine (ZMod p₂)) (aig : AIG (Fin m))
    {a b : Ty CryptoAtom} (op : CryptoOp a b) (refs : Wires w aig a) (input : Vector Bool m) :
    let n := aig.decls.size + gates w op
    (execute r W₁ W₂ aig op refs input).steps ≤
      n * (4*n + m + 10) + outputWidth w op * (n + 4) + 3 := by
  let out := compile r W₁ W₂ aig op refs
  have hs := compile_size hr h₁ h₂ W₁ W₂ aig op refs
  have he := CircuitExecution.evaluate_steps out.graph (outputs out.refs) input
  rw [outputs_length out.graph op] at he
  refine he.trans ?_
  gcongr

theorem execute_correct {m : Nat} (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
    [Module (ZMod r) H₁] [Module (ZMod r) H₂] [DecidableEq K] [DecidableEq M]
    (encodeK : K → BitVec w) (encodeM : M → BitVec w)
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts) (aig : AIG (Fin m)) {a b : Ty CryptoAtom} (op : CryptoOp a b)
    (refs : Wires w aig a) (input : Vector Bool m)
    (x : a.Value (cryptoBase (ZMod r) H₁ H₂ K M))
    (hx : Represents H₁ H₂ encodeK encodeM (fun i => input[i]) aig refs x)
    (hs : Safe (w := w) H₁ H₂ op x) :
    (execute r W₁ W₂ aig op refs input).value = portBits H₁ H₂ encodeK encodeM
      ((arithmetic (ZMod r) H₁ H₂ K M cost).execute op x) := by
  unfold execute
  rw [CircuitExecution.evaluate_correct]
  exact represented_outputs H₁ H₂ encodeK encodeM _ _ _ _
    (compile_correct H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm cost aig op refs _ x hx hs)

end Signatures.Runtime.CryptoCircuit
