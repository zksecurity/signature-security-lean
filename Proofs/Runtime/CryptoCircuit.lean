import Proofs.Runtime.CircuitWires
import Proofs.Runtime.EllipticCurveScale

/-! Circuit lowering for every constructor of the existing CryptoOp family.
This is an instruction compiler, not yet a compiler for the surrounding
typed heap, source program, or oracle/replay controller. -/

namespace Signatures.Runtime.CryptoCircuit

open Std.Sat Std.Tactic.BVDecide BVExpr.bitblast
open CircuitWires WeierstrassCurve

variable {A : Type} [Hashable A] [DecidableEq A] {w : Nat}

private theorem subtract_prefix (aig : AIG A) (input : AIG.BinaryRefVec aig w) :
    AIG.IsPrefix aig.decls (WordCircuit.subtract aig input).aig.decls := by
  unfold WordCircuit.subtract
  exact prefix_trans (AIG.LawfulOperator.isPrefix_aig (f := BVPred.mkUlt) _ _)
    (prefix_trans (AIG.LawfulVecOperator.isPrefix_aig (f := blastSub) _ _)
      (AIG.LawfulVecOperator.isPrefix_aig (f := AIG.RefVec.ite) _ _))

private theorem finOfNat_prefix (aig : AIG A) (input : AIG.RefVec aig w) (n : Nat) :
    AIG.IsPrefix aig.decls (WordCircuit.finOfNat aig input n).aig.decls := by
  unfold WordCircuit.finOfNat
  split
  · exact AIG.IsPrefix.rfl
  · exact AIG.LawfulVecOperator.isPrefix_aig (f := blastUmod) _ _

private theorem pointEq_prefix (p : Nat) (aig : AIG A) (x y : Fin 3 → AIG.RefVec aig w) :
    AIG.IsPrefix aig.decls (EllipticCurveCircuit.equal p aig x y).aig.decls :=
  prefix_trans (EllipticCurveCode.equalCode.compile p aig (EllipticCurveCircuit.pairRefs x y)).extension
    (AIG.LawfulOperator.isPrefix_aig (f := BVPred.mkEq) _ _)

variable {p₁ p₂ : Nat} [Fact p₁.Prime] [Fact p₂.Prime]

def compile (r : Nat) (W₁ : Affine (ZMod p₁)) (W₂ : Affine (ZMod p₂)) (aig : AIG A) :
    {a b : Ty CryptoAtom} → CryptoOp a b → Wires w aig a → Compiled w aig b
  | _, _, .zero, _ =>
    let out := PrimeFieldCircuit.zero aig
    ⟨out.result.aig, out.result.vec, out.extension⟩
  | _, _, .one, _ =>
    let out := PrimeFieldCircuit.one aig
    ⟨out.result.aig, out.result.vec, out.extension⟩
  | _, _, .add, x =>
    let out := FieldProgram.binary .add r aig ⟨x.1, x.2⟩
    ⟨out.result.aig, out.result.vec, out.extension⟩
  | _, _, .sub, x =>
    let out := FieldProgram.binary .sub r aig ⟨x.1, x.2⟩
    ⟨out.result.aig, out.result.vec, out.extension⟩
  | _, _, .mul, x =>
    let out := FieldProgram.binary .mul r aig ⟨x.1, x.2⟩
    ⟨out.result.aig, out.result.vec, out.extension⟩
  | _, _, .div, x =>
    let out := FieldProgram.binary .div r aig ⟨x.1, x.2⟩
    ⟨out.result.aig, out.result.vec, out.extension⟩
  | _, _, .neg, x =>
    let out := PrimeFieldCircuit.negate aig x r
    ⟨out.result.aig, out.result.vec, out.extension⟩
  | _, _, .zero₁, _ =>
    let out := EllipticCurveCircuit.zero aig
    ⟨out.graph, out.refs, out.extension⟩
  | _, _, .zero₂, _ =>
    let out := EllipticCurveCircuit.zero aig
    ⟨out.graph, out.refs, out.extension⟩
  | _, _, .add₁, x =>
    let out := EllipticCurveCircuit.add W₁ aig x.1 x.2
    ⟨out.graph, out.refs, out.extension⟩
  | _, _, .add₂, x =>
    let out := EllipticCurveCircuit.add W₂ aig x.1 x.2
    ⟨out.graph, out.refs, out.extension⟩
  | _, _, .sub₁, x =>
    let out := EllipticCurveCircuit.sub W₁ aig x.1 x.2
    ⟨out.graph, out.refs, out.extension⟩
  | _, _, .sub₂, x =>
    let out := EllipticCurveCircuit.sub W₂ aig x.1 x.2
    ⟨out.graph, out.refs, out.extension⟩
  | _, _, .scale₁, x =>
    let out := EllipticCurveCircuit.scale W₁ aig x.1 x.2
    ⟨out.graph, out.refs, out.extension⟩
  | _, _, .scale₂, x =>
    let out := EllipticCurveCircuit.scale W₂ aig x.1 x.2
    ⟨out.graph, out.refs, out.extension⟩
  | _, _, .point₁Eq, x =>
    let out := EllipticCurveCircuit.equal p₁ aig x.1 x.2
    ⟨out.aig, out.ref, pointEq_prefix p₁ aig x.1 x.2⟩
  | _, _, .point₂Eq, x =>
    let out := EllipticCurveCircuit.equal p₂ aig x.1 x.2
    ⟨out.aig, out.ref, pointEq_prefix p₂ aig x.1 x.2⟩
  | _, _, .scalarEq, x | _, _, .keyEq, x | _, _, .messageEq, x | _, _, .natEq, x =>
    let out := BVPred.mkEq aig ⟨x.1, x.2⟩
    ⟨out.aig, out.ref, AIG.LawfulOperator.isPrefix_aig (f := BVPred.mkEq) _ _⟩
  | _, _, .natLt, x =>
    let out := BVPred.mkUlt aig ⟨x.1, x.2⟩
    ⟨out.aig, out.ref, AIG.LawfulOperator.isPrefix_aig (f := BVPred.mkUlt) _ _⟩
  | _, _, .natAdd, x =>
    let out := blastAdd aig ⟨x.1, x.2⟩
    ⟨out.aig, out.vec, AIG.LawfulVecOperator.isPrefix_aig (f := blastAdd) _ _⟩
  | _, _, .natSub, x =>
    let out := WordCircuit.subtract aig ⟨x.1, x.2⟩
    ⟨out.aig, out.vec, subtract_prefix _ _⟩
  | _, _, .finVal _, x => ⟨aig, x, AIG.IsPrefix.rfl⟩
  | _, _, .finZero _, _ => ⟨aig, blastConst aig (BitVec.ofNat w 0), AIG.IsPrefix.rfl⟩
  | _, _, .finOfNat n, x =>
    let out := WordCircuit.finOfNat aig x n
    ⟨out.aig, out.vec, finOfNat_prefix _ _ _⟩

/-- Per-instruction circuit bounds, not assumed primitive prices. -/
def gates {a b : Ty CryptoAtom} (w : Nat) : CryptoOp a b → Nat
  | .zero | .one | .zero₁ | .zero₂ | .finVal _ | .finZero _ => 0
  | .add => FieldProgram.BinOp.add.gates w
  | .sub | .neg => FieldProgram.BinOp.sub.gates w
  | .mul => FieldProgram.BinOp.mul.gates w
  | .div => FieldProgram.BinOp.div.gates w
  | .add₁ | .add₂ => 4080*w^3 + 20897*w^2 + 12774*w
  | .sub₁ | .sub₂ => 4080*w^3 + 21056*w^2 + 12917*w
  | .scale₁ | .scale₂ => w * (8160*w^3 + 41794*w^2 + 25557*w)
  | .point₁Eq | .point₂Eq => 25*w
  | .scalarEq | .keyEq | .messageEq | .natEq => 4*w
  | .natLt => 6*w
  | .natAdd => 12*w
  | .natSub => 33*w
  | .finOfNat _ => 36*w*w + 7*w

theorem compile_size {r : Nat} [Fact r.Prime]
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (W₁ : Affine (ZMod p₁)) (W₂ : Affine (ZMod p₂)) (aig : AIG A)
    {a b : Ty CryptoAtom} (op : CryptoOp a b) (input : Wires w aig a) :
    (compile r W₁ W₂ aig op input).graph.decls.size ≤ aig.decls.size + gates w op := by
  cases op with
  | zero | one | zero₁ | zero₂ | finVal n | finZero n => simp [compile, gates, PrimeFieldCircuit.zero,
      PrimeFieldCircuit.one, EllipticCurveCircuit.zero]
  | add => exact FieldProgram.binary_size hr .add aig _
  | sub => exact FieldProgram.binary_size hr .sub aig _
  | mul => exact FieldProgram.binary_size hr .mul aig _
  | div => exact FieldProgram.binary_size hr .div aig _
  | neg => simpa only [compile, gates, FieldProgram.BinOp.gates, Nat.add_assoc] using PrimeFieldCircuit.negate_size aig input r
  | add₁ => exact EllipticCurveCircuit.add_size h₁ W₁ aig _ _
  | add₂ => exact EllipticCurveCircuit.add_size h₂ W₂ aig _ _
  | sub₁ => exact EllipticCurveCircuit.sub_size h₁ W₁ aig _ _
  | sub₂ => exact EllipticCurveCircuit.sub_size h₂ W₂ aig _ _
  | scale₁ => exact EllipticCurveCircuit.scale_size h₁ W₁ aig _ _
  | scale₂ => exact EllipticCurveCircuit.scale_size h₂ W₂ aig _ _
  | point₁Eq => exact EllipticCurveCircuit.equal_size h₁ aig _ _
  | point₂Eq => exact EllipticCurveCircuit.equal_size h₂ aig _ _
  | scalarEq | keyEq | messageEq | natEq => exact BitCircuit.eq_size aig _
  | natLt => exact BitCircuit.ult_size aig ⟨input.1, input.2⟩
  | natAdd => exact BitCircuit.add_size aig _
  | natSub => exact WordCircuit.subtract_size aig _
  | finOfNat n => simpa only [compile, gates, Nat.add_assoc] using WordCircuit.finOfNat_size aig input n

end Signatures.Runtime.CryptoCircuit
