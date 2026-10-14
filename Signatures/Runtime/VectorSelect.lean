import Signatures.Runtime.FieldCircuitVector

/-! Fixed-size multiplexer circuits. The selector is an input wire, not a Lean
branch on a secret value. All output words share a single extended graph. -/

namespace Signatures.Runtime.FieldProgram

open Std.Sat Std.Tactic.BVDecide BVExpr.bitblast
open PrimeFieldCircuit (Built Represents)

variable {A : Type} [Hashable A] [DecidableEq A] {w : Nat}

private def selectWord (aig : AIG A) (b : AIG.Ref aig) (x y : AIG.RefVec aig w) : Built aig w :=
  ⟨AIG.RefVec.ite aig ⟨b, x, y⟩,
    AIG.LawfulVecOperator.isPrefix_aig (f := AIG.RefVec.ite) aig ⟨b, x, y⟩⟩

private theorem selectWord_correct (aig : AIG A) (b : AIG.Ref aig) (x y : AIG.RefVec aig w)
    (assign : A → Bool) (d : Bool) (vx vy : BitVec w)
    (hb : AIG.denote assign ⟨aig, b⟩ = d) (hx : Represents assign aig x vx)
    (hy : Represents assign aig y vy) :
    Represents assign (selectWord aig b x y).result.aig (selectWord aig b x y).result.vec
      (if d then vx else vy) := by
  intro i hi
  rw [selectWord, AIG.RefVec.denote_ite]
  dsimp only
  rw [hb, hx i hi, hy i hi]
  cases d <;> rfl

def selectMany : {k : Nat} → (aig : AIG A) → AIG.Ref aig →
    (Fin k → AIG.RefVec aig w) → (Fin k → AIG.RefVec aig w) → Bundle aig w k
  | 0, aig, _, _, _ => ⟨aig, Fin.elim0, AIG.IsPrefix.rfl⟩
  | k + 1, aig, b, x, y =>
    let head := selectWord aig b (x 0) (y 0)
    let tail := selectMany head.result.aig (b.cast head.extension.size_le)
      (fun i : Fin k => head.cast (x i.succ)) (fun i => head.cast (y i.succ))
    ⟨tail.graph, Fin.cases (tail.cast head.result.vec) tail.refs,
      ⟨head.extension.size_le.trans tail.extension.size_le, fun i hi =>
        (tail.extension.idx_eq i (hi.trans_le head.extension.size_le)).trans (head.extension.idx_eq i hi)⟩⟩

theorem selectMany_size {k : Nat} (aig : AIG A) (b : AIG.Ref aig)
    (x y : Fin k → AIG.RefVec aig w) :
    (selectMany aig b x y).graph.decls.size ≤ aig.decls.size + k * (3 * w) := by
  induction k generalizing aig with
  | zero => simp [selectMany]
  | succ k ih =>
    dsimp only [selectMany]
    refine (ih _ _ _ _).trans ?_
    have hh := BitCircuit.ite_size aig ⟨b, x 0, y 0⟩
    change (selectWord aig b (x 0) (y 0)).result.aig.decls.size ≤ aig.decls.size + 3 * w at hh
    simp only [Nat.succ_mul]
    omega

theorem selectMany_correct {k : Nat} (aig : AIG A) (b : AIG.Ref aig)
    (x y : Fin k → AIG.RefVec aig w) (assign : A → Bool) (d : Bool)
    (vx vy : Fin k → BitVec w) (hb : AIG.denote assign ⟨aig, b⟩ = d)
    (hx : ∀ i, Represents assign aig (x i) (vx i)) (hy : ∀ i, Represents assign aig (y i) (vy i))
    (j : Fin k) :
    Represents assign (selectMany aig b x y).graph ((selectMany aig b x y).refs j)
      (if d then vx j else vy j) := by
  induction k generalizing aig with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    let head := selectWord aig b (x 0) (y 0)
    let tail := selectMany head.result.aig (b.cast head.extension.size_le)
      (fun i : Fin k => head.cast (x i.succ)) (fun i => head.cast (y i.succ))
    refine Fin.cases ?_ (fun i => ?_) j
    · exact tail.preserves assign head.result.vec _ (selectWord_correct aig b (x 0) (y 0) assign
        d (vx 0) (vy 0) hb (hx 0) (hy 0))
    · exact ih head.result.aig _ _ _ (fun i => vx i.succ) (fun i => vy i.succ)
        ((AIG.denote.eq_of_isPrefix ⟨aig, b⟩ _ head.extension).trans hb)
        (fun i => head.preserves assign (x i.succ) _ (hx i.succ))
        (fun i => head.preserves assign (y i.succ) _ (hy i.succ)) i

end Signatures.Runtime.FieldProgram
