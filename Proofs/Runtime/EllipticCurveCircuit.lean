import Proofs.Runtime.EllipticCurveCode
import Proofs.Runtime.FieldCircuitVector

/-! One shared Boolean circuit per elliptic-curve operation. Inputs and outputs
are canonical encodings of actual mathlib points; arbitrary invalid triples are
not silently treated as points. The base-field modulus need not be the scalar
modulus of a cryptographic subgroup. -/

namespace Signatures.Runtime.EllipticCurveCircuit

open Std.Sat Std.Tactic.BVDecide BVExpr.bitblast
open FieldProgram EllipticCurveCode WeierstrassCurve
open PrimeFieldCircuit (Represents)

attribute [local irreducible] compileMany Code.compile

variable {p w : Nat} [Fact p.Prime] {A : Type} [Hashable A] [DecidableEq A]

def RepresentsPoint {W : Affine (ZMod p)} (assign : A → Bool) (aig : AIG A)
    (refs : Fin 3 → AIG.RefVec aig w) (P : W.Point) : Prop :=
  ∀ i, Represents assign aig (refs i) (BitVec.ofNat w (encode P i).val)

def pairRefs {aig : AIG A} (x y : Fin 3 → AIG.RefVec aig w) : Fin 6 → AIG.RefVec aig w :=
  ![x 0, x 1, x 2, y 0, y 1, y 2]

theorem pairRefs_correct {W : Affine (ZMod p)} (assign : A → Bool) (aig : AIG A)
    (x y : Fin 3 → AIG.RefVec aig w) (P Q : W.Point)
    (hx : RepresentsPoint assign aig x P) (hy : RepresentsPoint assign aig y Q) (i : Fin 6) :
    Represents assign aig (pairRefs x y i) (BitVec.ofNat w (inputs P Q i).val) := by
  fin_cases i
  · exact hx 0
  · exact hx 1
  · exact hx 2
  · exact hy 0
  · exact hy 1
  · exact hy 2

def zero (aig : AIG A) : Bundle aig w 3 :=
  ⟨aig, fun _ => blastConst aig (BitVec.ofNat w 0), AIG.IsPrefix.rfl⟩

theorem zero_size (aig : AIG A) : (zero (w := w) aig).graph.decls.size = aig.decls.size := rfl

def neg (W : Affine (ZMod p)) (aig : AIG A) (x : Fin 3 → AIG.RefVec aig w) : Bundle aig w 3 :=
  compileMany p (negCode W) aig x

def add (W : Affine (ZMod p)) (aig : AIG A) (x y : Fin 3 → AIG.RefVec aig w) : Bundle aig w 3 :=
  compileMany p (addCode W) aig (pairRefs x y)

theorem zero_correct (W : Affine (ZMod p)) (aig : AIG A) (assign : A → Bool) :
    RepresentsPoint assign (zero (w := w) aig).graph (zero (w := w) aig).refs (0 : W.Point) := by
  intro i
  fin_cases i <;> simp [zero, encode, Represents, denote_blastConst]

theorem neg_correct (hfit : p * p ≤ 2 ^ w) (hp : 2 < p) (W : Affine (ZMod p))
    (aig : AIG A) (x : Fin 3 → AIG.RefVec aig w) (assign : A → Bool) (P : W.Point)
    (hx : RepresentsPoint assign aig x P) :
    RepresentsPoint assign (neg W aig x).graph (neg W aig x).refs (-P) := by
  intro i
  simpa only [neg, negCode_correct] using compileMany_correct hfit hp (negCode W) aig x assign (encode P) hx i

theorem add_correct (hfit : p * p ≤ 2 ^ w) (hp : 2 < p) (W : Affine (ZMod p))
    (aig : AIG A) (x y : Fin 3 → AIG.RefVec aig w) (assign : A → Bool) (P Q : W.Point)
    (hx : RepresentsPoint assign aig x P) (hy : RepresentsPoint assign aig y Q) :
    RepresentsPoint assign (add W aig x y).graph (add W aig x y).refs (P + Q) := by
  intro i
  simpa only [add, addCode_correct] using compileMany_correct hfit hp (addCode W) aig (pairRefs x y)
    assign (inputs P Q) (pairRefs_correct assign aig x y P Q hx hy) i

theorem neg_size (hfit : p * p ≤ 2 ^ w) (W : Affine (ZMod p))
    (aig : AIG A) (x : Fin 3 → AIG.RefVec aig w) :
    (neg W aig x).graph.decls.size ≤ aig.decls.size + 159 * w^2 + 143 * w := by
  have := compileMany_size hfit (negCode W) aig x
  rw [negCode_gates] at this
  simpa only [neg, pow_two, Nat.add_assoc, Nat.mul_assoc] using this

theorem add_size (hfit : p * p ≤ 2 ^ w) (W : Affine (ZMod p))
    (aig : AIG A) (x y : Fin 3 → AIG.RefVec aig w) :
    (add W aig x y).graph.decls.size ≤ aig.decls.size +
      (4080 * w^3 + 20897 * w^2 + 12774 * w) := by
  simpa only [add, addCode_gates] using compileMany_size hfit (addCode W) aig (pairRefs x y)

attribute [local irreducible] add neg

private def finishSub (W : Affine (ZMod p)) {aig : AIG A} (nq : Bundle aig w 3)
    (x : Fin 3 → AIG.RefVec aig w) : Bundle aig w 3 :=
  nq.chain (add W nq.graph (fun i => nq.cast (x i)) nq.refs)

private theorem finishSub_correct (hfit : p * p ≤ 2 ^ w) (hp : 2 < p) (W : Affine (ZMod p))
    (aig : AIG A) (nq : Bundle aig w 3) (x : Fin 3 → AIG.RefVec aig w) (assign : A → Bool)
    (P Q : W.Point) (hx : RepresentsPoint assign aig x P)
    (hy : RepresentsPoint assign nq.graph nq.refs (-Q)) :
    RepresentsPoint assign (finishSub W nq x).graph (finishSub W nq x).refs (P - Q) := by
  have hnx : RepresentsPoint assign nq.graph (fun i => nq.cast (x i)) P :=
    fun i => nq.preserves assign (x i) _ (hx i)
  exact nq.chain_correct (add W nq.graph (fun i => nq.cast (x i)) nq.refs) assign
    (fun i => BitVec.ofNat w (encode (P + -Q) i).val)
    (add_correct hfit hp W nq.graph (fun i => nq.cast (x i)) nq.refs assign P (-Q) hnx hy)

attribute [local irreducible] finishSub

def sub (W : Affine (ZMod p)) (aig : AIG A) (x y : Fin 3 → AIG.RefVec aig w) : Bundle aig w 3 :=
  finishSub W (neg W aig y) x

theorem sub_correct (hfit : p * p ≤ 2 ^ w) (hp : 2 < p) (W : Affine (ZMod p))
    (aig : AIG A) (x y : Fin 3 → AIG.RefVec aig w) (assign : A → Bool) (P Q : W.Point)
    (hx : RepresentsPoint assign aig x P) (hy : RepresentsPoint assign aig y Q) :
    RepresentsPoint assign (sub W aig x y).graph (sub W aig x y).refs (P - Q) :=
  finishSub_correct hfit hp W aig (neg W aig y) x assign P Q hx (neg_correct hfit hp W aig y assign Q hy)

theorem sub_size (hfit : p * p ≤ 2 ^ w) (W : Affine (ZMod p))
    (aig : AIG A) (x y : Fin 3 → AIG.RefVec aig w) :
    (sub W aig x y).graph.decls.size ≤ aig.decls.size +
      (4080 * w^3 + 21056 * w^2 + 12917 * w) := by
  unfold sub finishSub
  rw [Bundle.chain_size]
  refine (add_size hfit W (neg W aig y).graph (fun i => (neg W aig y).cast (x i)) (neg W aig y).refs).trans ?_
  have := neg_size hfit W aig y
  omega

def equal (p : Nat) (aig : AIG A) (x y : Fin 3 → AIG.RefVec aig w) : AIG.Entrypoint A :=
  let out := equalCode.compile p aig (pairRefs x y)
  BVPred.mkEq out.result.aig ⟨out.result.vec, blastConst out.result.aig (BitVec.ofNat w 1)⟩

theorem equal_size (hfit : p * p ≤ 2 ^ w) (aig : AIG A) (x y : Fin 3 → AIG.RefVec aig w) :
    (equal p aig x y).aig.decls.size ≤ aig.decls.size + 25 * w := by
  unfold equal
  refine (BitCircuit.eq_size _ _).trans ?_
  have := equalCode.compile_size hfit aig (pairRefs x y)
  rw [equalCode_gates] at this
  omega

theorem equal_correct (hfit : p * p ≤ 2 ^ w) (hp : 2 < p) (W : Affine (ZMod p))
    (aig : AIG A) (x y : Fin 3 → AIG.RefVec aig w) (assign : A → Bool) (P Q : W.Point)
    (hx : RepresentsPoint assign aig x P) (hy : RepresentsPoint assign aig y Q) :
    AIG.denote assign (equal p aig x y) = decide (P = Q) := by
  let out := equalCode.compile p aig (pairRefs x y)
  have hc := equalCode.compile_correct hfit hp aig (pairRefs x y) assign (inputs P Q)
    (pairRefs_correct assign aig x y P Q hx hy)
  rw [equalCode_correct] at hc
  have he := PrimeFieldCircuit.eq_correct ((Nat.le_mul_self p).trans hfit) out.result.aig
    ⟨out.result.vec, blastConst out.result.aig (BitVec.ofNat w 1)⟩ assign
    (if P = Q then 1 else 0) 1 hc (by simpa only [ZMod.val_one, Represents] using denote_blastConst _ (BitVec.ofNat w 1) assign)
  by_cases h : P = Q <;> simpa only [equal, out, h, ite_true, ite_false, decide_true,
    decide_false, zero_ne_one] using he

end Signatures.Runtime.EllipticCurveCircuit
