import Proofs.Runtime.CryptoCircuit
import Proofs.Runtime.NaturalRange

/-! Instruction-level refinement to the existing arithmetic semantics. A wire
representing a Nat or Fin value includes a no-truncation invariant. Keys and
messages use explicit injective codecs; arbitrary encodings are not assumed. -/

namespace Signatures.Runtime.CryptoCircuit

open Std.Sat Std.Tactic.BVDecide BVExpr.bitblast
open CircuitWires WeierstrassCurve

variable {r p₁ p₂ w : Nat} [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)}
  {K M A : Type} [Hashable A] [DecidableEq A]

def Represents (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
    (encodeK : K → BitVec w) (encodeM : M → BitVec w) (assign : A → Bool) (aig : AIG A) :
    {t : Ty CryptoAtom} → Wires w aig t → t.Value (cryptoBase (ZMod r) H₁ H₂ K M) → Prop
  | .atom .scalar, refs, x => PrimeFieldCircuit.Represents assign aig refs (BitVec.ofNat w x.val)
  | .atom .point₁, refs, x => EllipticCurveCircuit.RepresentsPoint assign aig refs (x : W₁.Point)
  | .atom .point₂, refs, x => EllipticCurveCircuit.RepresentsPoint assign aig refs (x : W₂.Point)
  | .atom .key, refs, x => PrimeFieldCircuit.Represents assign aig refs (encodeK x)
  | .atom .message, refs, x => PrimeFieldCircuit.Represents assign aig refs (encodeM x)
  | .atom (.fin _), refs, x => WordCircuit.RepresentsNat assign aig refs x.val
  | .unit, _, _ => True
  | .bool, ref, x => AIG.denote assign ⟨aig, ref⟩ = x
  | .nat, refs, x => WordCircuit.RepresentsNat assign aig refs x
  | .pair _ _, refs, x => Represents H₁ H₂ encodeK encodeM assign aig refs.1 x.1 ∧
      Represents H₁ H₂ encodeK encodeM assign aig refs.2 x.2
  | .list _, refs, xs => List.Forall₂ (Represents H₁ H₂ encodeK encodeM assign aig) refs xs

variable (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
  (encodeK : K → BitVec w) (encodeM : M → BitVec w)

omit [Fact r.Prime] in
theorem represents_preserved {aig next : AIG A} (h : AIG.IsPrefix aig.decls next.decls)
    (assign : A → Bool) {t : Ty CryptoAtom} (refs : Wires w aig t)
    (x : t.Value (cryptoBase (ZMod r) H₁ H₂ K M))
    (hx : Represents H₁ H₂ encodeK encodeM assign aig refs x) :
    Represents H₁ H₂ encodeK encodeM assign next (CircuitWires.cast h refs) x := by
  have word (refs : AIG.RefVec aig w) (value : BitVec w)
      (hv : PrimeFieldCircuit.Represents assign aig refs value) :
      PrimeFieldCircuit.Represents assign next (refs.cast h.size_le) value := by
    intro i hi
    rw [AIG.RefVec.get_cast]
    exact (AIG.denote.eq_of_isPrefix ⟨aig, refs.get i hi⟩ _ h).trans (hv i hi)
  induction t with
  | atom a =>
    cases a with
    | scalar | key | message => exact word _ _ hx
    | point₁ | point₂ => exact fun i => word _ _ (hx i)
    | fin n => exact ⟨hx.1, word _ _ hx.2⟩
  | unit => trivial
  | bool => exact (AIG.denote.eq_of_isPrefix ⟨aig, refs⟩ _ h).trans hx
  | nat => exact ⟨hx.1, word _ _ hx.2⟩
  | pair a b iha ihb => exact ⟨iha refs.1 x.1 hx.1, ihb refs.2 x.2 hx.2⟩
  | list a ih =>
    change List.Forall₂ _ (refs.map (CircuitWires.cast h)) x
    induction hx with
    | nil => exact .nil
    | cons hhead htail ihtail => exact .cons (ih _ _ hhead) ihtail

/-- The one extra obligation beyond input representation: a natural sum must fit. -/
def Safe {a b : Ty CryptoAtom} (op : CryptoOp a b)
    (x : a.Value (cryptoBase (ZMod r) H₁ H₂ K M)) : Prop :=
  match op with
  | .natAdd => x.1 + x.2 < 2^w
  | _ => True

variable [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂]

/-- The source expression's budget implies the dispatcher's overflow obligation;
it need not be postulated separately for each executed natural addition. -/
theorem safe_of_expr_budget (cost : PrimitiveCosts) {Γ : List (Ty CryptoAtom)} {a b : Ty CryptoAtom}
    (op : CryptoOp a b) (arg : Expr CryptoOp Γ a) (bits : Nat)
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) (he : NaturalRange.EnvBound bits env)
    (hb : bits + ((Expr.op op arg).run (arithmetic (ZMod r) H₁ H₂ K M cost) env).steps ≤ w) :
    Safe (w := w) H₁ H₂ op (arg.run (arithmetic (ZMod r) H₁ H₂ K M cost) env).value := by
  have h := NaturalRange.expr_trace_bound cost (Expr.op op arg) bits w env he hb
  cases op with
  | natAdd => exact h.2
  | _ => trivial

theorem compile_correct (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts) (aig : AIG A) {a b : Ty CryptoAtom} (op : CryptoOp a b)
    (refs : Wires w aig a) (assign : A → Bool)
    (x : a.Value (cryptoBase (ZMod r) H₁ H₂ K M))
    (hx : Represents H₁ H₂ encodeK encodeM assign aig refs x)
    (hs : Safe (w := w) H₁ H₂ op x) :
    Represents H₁ H₂ encodeK encodeM assign (compile r W₁ W₂ aig op refs).graph
      (compile r W₁ W₂ aig op refs).refs
      ((arithmetic (ZMod r) H₁ H₂ K M cost).execute op x) := by
  have hrf : r ≤ 2^w := (Nat.le_mul_self r).trans hr
  cases op with
  | zero => exact PrimeFieldCircuit.zero_correct aig assign
  | one => exact PrimeFieldCircuit.one_correct aig assign
  | add => exact FieldProgram.binary_correct hr hr' .add aig _ assign x.1 x.2 hx.1 hx.2
  | sub => exact FieldProgram.binary_correct hr hr' .sub aig _ assign x.1 x.2 hx.1 hx.2
  | mul => exact FieldProgram.binary_correct hr hr' .mul aig _ assign x.1 x.2 hx.1 hx.2
  | div => exact FieldProgram.binary_correct hr hr' .div aig _ assign x.1 x.2 hx.1 hx.2
  | neg => exact PrimeFieldCircuit.negate_correct hr aig refs assign x hx
  | zero₁ => exact EllipticCurveCircuit.zero_correct W₁ aig assign
  | zero₂ => exact EllipticCurveCircuit.zero_correct W₂ aig assign
  | add₁ => exact EllipticCurveCircuit.add_correct h₁ h₁' W₁ aig _ _ assign x.1 x.2 hx.1 hx.2
  | add₂ => exact EllipticCurveCircuit.add_correct h₂ h₂' W₂ aig _ _ assign x.1 x.2 hx.1 hx.2
  | sub₁ => exact EllipticCurveCircuit.sub_correct h₁ h₁' W₁ aig _ _ assign x.1 x.2 hx.1 hx.2
  | sub₂ => exact EllipticCurveCircuit.sub_correct h₂ h₂' W₂ aig _ _ assign x.1 x.2 hx.1 hx.2
  | scale₁ => exact EllipticCurveCircuit.scale_correct h₁ h₁' hrf W₁ H₁ aig _ _ assign x.1 x.2 hx.1 hx.2
  | scale₂ => exact EllipticCurveCircuit.scale_correct h₂ h₂' hrf W₂ H₂ aig _ _ assign x.1 x.2 hx.1 hx.2
  | scalarEq => exact PrimeFieldCircuit.eq_correct hrf aig _ assign x.1 x.2 hx.1 hx.2
  | point₁Eq =>
    simpa only [Represents, compile, arithmetic, Subtype.coe_inj] using
      EllipticCurveCircuit.equal_correct h₁ h₁' W₁ aig refs.1 refs.2 assign x.1 x.2 hx.1 hx.2
  | point₂Eq =>
    simpa only [Represents, compile, arithmetic, Subtype.coe_inj] using
      EllipticCurveCircuit.equal_correct h₂ h₂' W₂ aig refs.1 refs.2 assign x.1 x.2 hx.1 hx.2
  | keyEq => exact WordCircuit.eq_encoded_correct encodeK hk aig _ assign x.1 x.2 hx.1 hx.2
  | messageEq => exact WordCircuit.eq_encoded_correct encodeM hm aig _ assign x.1 x.2 hx.1 hx.2
  | natAdd => exact WordCircuit.add_correct aig _ assign x.1 x.2 hs hx.1.2 hx.2.2
  | natSub => exact WordCircuit.subtract_correct aig _ assign x.1 x.2 hx.1.1 hx.2.1 hx.1.2 hx.2.2
  | natEq => exact WordCircuit.eq_correct aig _ assign x.1 x.2 hx.1.1 hx.2.1 hx.1.2 hx.2.2
  | natLt => exact WordCircuit.lt_correct aig ⟨refs.1, refs.2⟩ assign x.1 x.2 hx.1.1 hx.2.1 hx.1.2 hx.2.2
  | finVal n => exact hx
  | finZero n => exact WordCircuit.finZero_correct aig assign n
  | finOfNat n => exact WordCircuit.finOfNat_correct aig refs n assign x hx.1 hx.2

end Signatures.Runtime.CryptoCircuit
