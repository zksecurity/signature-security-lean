import Signatures.Runtime.EllipticCurveCircuit
import Signatures.Runtime.VectorSelect
import Signatures.Runtime.WordCircuit
import Mathlib.Algebra.Module.ZMod

/-! Secret-bit scalar multiplication. Every bit builds a doubling, an addition,
and a multiplexer; circuit topology does not branch on the scalar's value. -/

namespace Signatures.Runtime.EllipticCurveCircuit

open Std.Sat Std.Tactic.BVDecide BVExpr.bitblast
open FieldProgram EllipticCurveCode WeierstrassCurve

variable {p w : Nat} [Fact p.Prime] {A : Type} [Hashable A] [DecidableEq A]

attribute [local irreducible] add selectMany

theorem selectPoint_correct (W : Affine (ZMod p)) (aig : AIG A) (b : AIG.Ref aig)
    (x y : Fin 3 → AIG.RefVec aig w) (assign : A → Bool) (d : Bool) (P Q : W.Point)
    (hb : AIG.denote assign ⟨aig, b⟩ = d) (hx : RepresentsPoint assign aig x P)
    (hy : RepresentsPoint assign aig y Q) :
    RepresentsPoint assign (selectMany aig b x y).graph (selectMany aig b x y).refs (if d then P else Q) := by
  intro i
  have h := selectMany_correct aig b x y assign d (fun i => BitVec.ofNat w (encode P i).val)
    (fun i => BitVec.ofNat w (encode Q i).val) hb hx hy i
  cases d <;> exact h

private def finishStep (W : Affine (ZMod p)) {aig : AIG A} (dbl : Bundle aig w 3)
    (b : AIG.Ref aig) (base : Fin 3 → AIG.RefVec aig w) : Bundle aig w 3 :=
  let plus := add W dbl.graph dbl.refs (fun i => dbl.cast (base i))
  dbl.chain (plus.chain (selectMany plus.graph (plus.castRef (dbl.castRef b))
    plus.refs (fun i => plus.cast (dbl.refs i))))

private theorem finishStep_correct (hfit : p * p ≤ 2 ^ w) (hp : 2 < p) (W : Affine (ZMod p))
    (aig : AIG A) (dbl : Bundle aig w 3) (b : AIG.Ref aig) (base : Fin 3 → AIG.RefVec aig w)
    (assign : A → Bool) (d : Bool) (D P : W.Point) (hb : AIG.denote assign ⟨aig, b⟩ = d)
    (hd : RepresentsPoint assign dbl.graph dbl.refs D) (hP : RepresentsPoint assign aig base P) :
    RepresentsPoint assign (finishStep W dbl b base).graph (finishStep W dbl b base).refs
      (if d then D + P else D) := by
  let plus := add W dbl.graph dbl.refs (fun i => dbl.cast (base i))
  have ha : RepresentsPoint assign plus.graph plus.refs (D + P) :=
    add_correct hfit hp W dbl.graph dbl.refs _ assign D P hd (fun i => dbl.preserves assign _ _ (hP i))
  have hs := selectPoint_correct W plus.graph (plus.castRef (dbl.castRef b)) plus.refs
    (fun i => plus.cast (dbl.refs i)) assign d (D + P) D
    ((plus.preservesRef assign _).trans ((dbl.preservesRef assign b).trans hb)) ha
    (fun i => plus.preserves assign _ _ (hd i))
  exact dbl.chain_correct _ assign _ (plus.chain_correct _ assign _ hs)

private theorem finishStep_size (hfit : p * p ≤ 2 ^ w) (W : Affine (ZMod p))
    (aig : AIG A) (dbl : Bundle aig w 3) (b : AIG.Ref aig) (base : Fin 3 → AIG.RefVec aig w) :
    (finishStep W dbl b base).graph.decls.size ≤ dbl.graph.decls.size +
      (4080 * w^3 + 20897 * w^2 + 12783 * w) := by
  unfold finishStep
  rw [Bundle.chain_size, Bundle.chain_size]
  refine (selectMany_size _ _ _ _).trans ?_
  have := add_size hfit W dbl.graph dbl.refs (fun i => dbl.cast (base i))
  omega

attribute [local irreducible] finishStep

def scaleStep (W : Affine (ZMod p)) (aig : AIG A) (b : AIG.Ref aig)
    (base acc : Fin 3 → AIG.RefVec aig w) : Bundle aig w 3 :=
  finishStep W (add W aig acc acc) b base

theorem scaleStep_correct (hfit : p * p ≤ 2 ^ w) (hp : 2 < p) (W : Affine (ZMod p))
    (aig : AIG A) (b : AIG.Ref aig) (base acc : Fin 3 → AIG.RefVec aig w)
    (assign : A → Bool) (d : Bool) (P Q : W.Point) (hb : AIG.denote assign ⟨aig, b⟩ = d)
    (hP : RepresentsPoint assign aig base P) (hQ : RepresentsPoint assign aig acc Q) :
    RepresentsPoint assign (scaleStep W aig b base acc).graph (scaleStep W aig b base acc).refs
      (if d then Q + Q + P else Q + Q) :=
  finishStep_correct hfit hp W aig (add W aig acc acc) b base assign d (Q + Q) P hb
    (add_correct hfit hp W aig acc acc assign Q Q hQ hQ) hP

theorem scaleStep_size (hfit : p * p ≤ 2 ^ w) (W : Affine (ZMod p))
    (aig : AIG A) (b : AIG.Ref aig) (base acc : Fin 3 → AIG.RefVec aig w) :
    (scaleStep W aig b base acc).graph.decls.size ≤ aig.decls.size +
      (8160 * w^3 + 41794 * w^2 + 25557 * w) := by
  refine (finishStep_size hfit W aig (add W aig acc acc) b base).trans ?_
  have := add_size hfit W aig acc acc
  omega

attribute [local irreducible] scaleStep

private def appendStep (W : Affine (ZMod p)) {aig : AIG A} (tail : Bundle aig w 3)
    (b : AIG.Ref aig) (base : Fin 3 → AIG.RefVec aig w) : Bundle aig w 3 :=
  tail.chain (scaleStep W tail.graph (tail.castRef b) (fun i => tail.cast (base i)) tail.refs)

private theorem appendStep_size (hfit : p * p ≤ 2 ^ w) (W : Affine (ZMod p))
    (aig : AIG A) (tail : Bundle aig w 3) (b : AIG.Ref aig) (base : Fin 3 → AIG.RefVec aig w) :
    (appendStep W tail b base).graph.decls.size ≤ tail.graph.decls.size +
      (8160 * w^3 + 41794 * w^2 + 25557 * w) := by
  unfold appendStep
  rw [Bundle.chain_size]
  exact scaleStep_size hfit W tail.graph (tail.castRef b) (fun i => tail.cast (base i)) tail.refs

private theorem appendStep_correct (hfit : p * p ≤ 2 ^ w) (hp : 2 < p) (W : Affine (ZMod p))
    (aig : AIG A) (tail : Bundle aig w 3) (b : AIG.Ref aig) (base : Fin 3 → AIG.RefVec aig w)
    (assign : A → Bool) (P Q : W.Point) (hP : RepresentsPoint assign aig base P)
    (hQ : RepresentsPoint assign tail.graph tail.refs Q) :
    RepresentsPoint assign (appendStep W tail b base).graph (appendStep W tail b base).refs
      (if AIG.denote assign ⟨aig, b⟩ then Q + Q + P else Q + Q) :=
  tail.chain_correct _ assign _ (scaleStep_correct hfit hp W tail.graph (tail.castRef b)
    (fun i => tail.cast (base i)) tail.refs assign (AIG.denote assign ⟨aig, b⟩) P Q
    (tail.preservesRef assign b) (fun i => tail.preserves assign _ _ (hP i)) hQ)

attribute [local irreducible] appendStep

/-- Input references are ordered least-significant bit first. -/
def scaleBits (W : Affine (ZMod p)) (aig : AIG A) (base : Fin 3 → AIG.RefVec aig w) :
    List (AIG.Ref aig) → Bundle aig w 3
  | [] => zero aig
  | b :: bs => appendStep W (scaleBits W aig base bs) b base

theorem scaleBits_size (hfit : p * p ≤ 2 ^ w) (W : Affine (ZMod p))
    (aig : AIG A) (base : Fin 3 → AIG.RefVec aig w) (bs : List (AIG.Ref aig)) :
    (scaleBits W aig base bs).graph.decls.size ≤ aig.decls.size +
      bs.length * (8160 * w^3 + 41794 * w^2 + 25557 * w) := by
  induction bs with
  | nil => simp [scaleBits, zero]
  | cons b bs ih =>
    simp only [scaleBits, List.length_cons]
    refine (appendStep_size hfit _ _ _ _ _).trans ?_
    nlinarith

theorem scaleBits_correct (hfit : p * p ≤ 2 ^ w) (hp : 2 < p) (W : Affine (ZMod p))
    (aig : AIG A) (base : Fin 3 → AIG.RefVec aig w) (bs : List (AIG.Ref aig))
    (assign : A → Bool) (P : W.Point) (hP : RepresentsPoint assign aig base P) :
    RepresentsPoint assign (scaleBits W aig base bs).graph (scaleBits W aig base bs).refs
      (PrimeFieldCircuit.exponent (bs.map (fun b => AIG.denote assign ⟨aig, b⟩)) • P) := by
  induction bs with
  | nil => simpa only [scaleBits, List.map_nil, PrimeFieldCircuit.exponent, zero_nsmul] using zero_correct W aig assign
  | cons b bs ih =>
    let tail := scaleBits W aig base bs
    let n := PrimeFieldCircuit.exponent (bs.map (fun b => AIG.denote assign ⟨aig, b⟩))
    have hs := appendStep_correct hfit hp W aig tail b base assign P (n • P) hP ih
    have he : (if AIG.denote assign ⟨aig, b⟩ then n • P + n • P + P else n • P + n • P) =
        PrimeFieldCircuit.exponent ((b :: bs).map (fun b => AIG.denote assign ⟨aig, b⟩)) • P := by
      cases h : AIG.denote assign ⟨aig, b⟩ <;>
        simp [List.map_cons, PrimeFieldCircuit.exponent, n, h, add_nsmul]
    rw [he] at hs
    exact hs

attribute [local irreducible] scaleBits

/-- The scalar width is independent of the coordinate width. -/
def scale {v : Nat} (W : Affine (ZMod p)) (aig : AIG A)
    (scalar : AIG.RefVec aig v) (base : Fin 3 → AIG.RefVec aig w) : Bundle aig w 3 :=
  scaleBits W aig base (List.ofFn (fun i : Fin v => scalar.get i i.isLt))

theorem scale_size {v : Nat} (hfit : p * p ≤ 2 ^ w) (W : Affine (ZMod p))
    (aig : AIG A) (scalar : AIG.RefVec aig v) (base : Fin 3 → AIG.RefVec aig w) :
    (scale W aig scalar base).graph.decls.size ≤ aig.decls.size +
      v * (8160 * w^3 + 41794 * w^2 + 25557 * w) := by
  simpa only [scale, List.length_ofFn] using
    scaleBits_size hfit W aig base (List.ofFn (fun i : Fin v => scalar.get i i.isLt))

theorem scale_word_correct {v : Nat} (hfit : p * p ≤ 2 ^ w) (hp : 2 < p)
    (W : Affine (ZMod p)) (aig : AIG A) (scalar : AIG.RefVec aig v)
    (base : Fin 3 → AIG.RefVec aig w) (assign : A → Bool) (x : BitVec v) (P : W.Point)
    (hx : PrimeFieldCircuit.Represents assign aig scalar x) (hP : RepresentsPoint assign aig base P) :
    RepresentsPoint assign (scale W aig scalar base).graph (scale W aig scalar base).refs (x.toNat • P) := by
  have hbits : (List.ofFn (fun i : Fin v => scalar.get i i.isLt)).map
      (fun b => AIG.denote assign ⟨aig, b⟩) = List.ofFn (fun i : Fin v => x.getLsbD i) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact hx i i.isLt
  have h := scaleBits_correct hfit hp W aig base
    (List.ofFn (fun i : Fin v => scalar.get i i.isLt)) assign P hP
  rw [hbits, WordCircuit.exponent_word] at h
  exact h

/-- A subgroup killed by `r` has the required scalar action. This does not assert
its size, choose a generator, or assume discrete-log hardness. -/
abbrev subgroupModule {r : Nat} (W : Affine (ZMod p)) (H : AddSubgroup W.Point)
    (h : ∀ P : H, r • P = 0) : Module (ZMod r) H :=
  AddCommGroup.zmodModule h

/-- Scalar-field semantics on a curve subgroup; the base prime `p` and scalar
prime `r` may differ. Only the subgroup, not the whole curve, needs this action. -/
theorem scale_correct {r v : Nat} [Fact r.Prime] (hfit : p * p ≤ 2 ^ w) (hp : 2 < p)
    (hscalar : r ≤ 2 ^ v) (W : Affine (ZMod p)) (H : AddSubgroup W.Point) [Module (ZMod r) H]
    (aig : AIG A) (scalar : AIG.RefVec aig v) (base : Fin 3 → AIG.RefVec aig w)
    (assign : A → Bool) (x : ZMod r) (P : H)
    (hx : PrimeFieldCircuit.Represents assign aig scalar (BitVec.ofNat v x.val))
    (hP : RepresentsPoint assign aig base (P : W.Point)) :
    RepresentsPoint assign (scale W aig scalar base).graph (scale W aig scalar base).refs
      ((x • P : H) : W.Point) := by
  have hs : x.val • P = x • P := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod r), ZMod.natCast_zmod_val]
  have h := scale_word_correct hfit hp W aig scalar base assign (BitVec.ofNat v x.val) P hx hP
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (x.val_lt.trans_le hscalar)] at h
  have he : x.val • (P : W.Point) = ((x • P : H) : W.Point) :=
    (map_nsmul H.subtype x.val P).symm.trans (congrArg H.subtype hs)
  rwa [he] at h

end Signatures.Runtime.EllipticCurveCircuit
