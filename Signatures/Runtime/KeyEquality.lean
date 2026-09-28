import Signatures.Runtime.Weights
import Signatures.Runtime.LookupExpr

/-! Executed equality tests for each AGM key encoding. In particular, comparing an OOPS
or Proximity key charges both the topic comparison and the bounded-index projections. -/

namespace Signatures.Runtime.AGM.KeyEquality

def bls : Expr CryptoOp [key, key] .bool :=
  .op .keyEq (.pair (.var .here) (.var (.there .here)))

def oops (d : Nat) : Expr CryptoOp [Weights.oopsKey d, Weights.oopsKey d] .bool :=
  .branch (.op .keyEq (.pair (.fst (.var .here)) (.fst (.var (.there .here)))))
    (.op .natEq (.pair (.op (.finVal d) (.snd (.var .here)))
      (.op (.finVal d) (.snd (.var (.there .here)))))) (.bool false)

def proximity (ell : Nat) :
    Expr CryptoOp [Weights.proximityKey ell, Weights.proximityKey ell] .bool :=
  .branch (.op .keyEq (.pair (.snd (.var .here)) (.snd (.var (.there .here)))))
    (.op .natEq (.pair (.op (.finVal ell) (.fst (.var .here)))
      (.op (.finVal ell) (.fst (.var (.there .here)))))) (.bool false)

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem bls_value (cost : PrimitiveCosts) (x y : K) :
    bls.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y) := rfl

theorem bls_steps (cost : PrimitiveCosts) (x y : K) :
    (bls.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps = cost.keyEq + 5 := by
  simp [bls, Expr.run, Var.depth, arithmetic, CryptoOp.price]
  omega

theorem oops_value (cost : PrimitiveCosts) (d : Nat) (x y : K × Fin (d + 1)) :
    (oops d).denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y) := by
  by_cases h : x.1 = y.1 <;>
    simp [oops, Expr.denote, Var.get, arithmetic, h, Prod.ext_iff, Fin.ext_iff]
  exact decide_eq_decide.mpr Iff.rfl

theorem oops_steps_le (cost : PrimitiveCosts) (d : Nat) (x y : K × Fin (d + 1)) :
    ((oops d).run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤
      cost.keyEq + 3 * cost.natOp + 17 := by
  by_cases h : x.1 = y.1 <;>
    simp [oops, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price, h] <;> omega

theorem proximity_value (cost : PrimitiveCosts) (ell : Nat) (x y : Fin (ell + 1) × K) :
    (proximity ell).denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y) := by
  by_cases h : x.2 = y.2 <;>
    simp [proximity, Expr.denote, Var.get, arithmetic, h, Prod.ext_iff, Fin.ext_iff]
  exact decide_eq_decide.mpr Iff.rfl

theorem proximity_steps_le (cost : PrimitiveCosts) (ell : Nat) (x y : Fin (ell + 1) × K) :
    ((proximity ell).run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤
      cost.keyEq + 3 * cost.natOp + 17 := by
  by_cases h : x.2 = y.2 <;>
    simp [proximity, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price, h] <;> omega

end Signatures.Runtime.AGM.KeyEquality
