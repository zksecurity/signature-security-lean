import Signatures.Runtime.Arithmetic
import Signatures.Runtime.Weakening
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Table-weighted scalar sums execute the supplied first-order weight expression at every
row. The expression is syntax, not a host-language callback or a whole-sum primitive. -/

namespace Signatures.Runtime.AGM

variable {indexTy messageTy : Ty CryptoAtom}

def weightedSumBody (weight : Expr CryptoOp [indexTy, messageTy] scalar) :
    Expr CryptoOp [.pair indexTy scalar, scalar, messageTy, .list (.pair indexTy scalar)] scalar :=
  .letE (.var (.there (.there .here)))
    (.letE (.fst (.var (.there .here)))
      (.letE (weight.weakenTail
        [.pair indexTy scalar, scalar, messageTy, .list (.pair indexTy scalar)])
        (.op .add (.pair (.var (.there (.there (.there (.there .here)))))
          (.op .mul (.pair (.snd (.var (.there (.there (.there .here))))) (.var .here)))))))

def weightedSum (weight : Expr CryptoOp [indexTy, messageTy] scalar) :
    Expr CryptoOp [messageTy, .list (.pair indexTy scalar)] scalar :=
  .fold (.var (.there .here)) (.op .zero .unit) (weightedSumBody weight)

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem weightedSumBody_run (cost : PrimitiveCosts)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (p : indexTy.Value (cryptoBase F G₁ G₂ K M) × F) (acc : F)
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (xs : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) :
    (weightedSumBody weight).run (arithmetic F G₁ G₂ K M cost) (p, acc, m, xs, ()) =
      let r := weight.run (arithmetic F G₁ G₂ K M cost) (p.1, m, ())
      ⟨acc + p.2 * r.value, r.steps + 2 * cost.field + 24⟩ := by
  have hw := weight.weakenTail_run
    (Δ := [.pair indexTy scalar, scalar, messageTy, .list (.pair indexTy scalar)])
    (arithmetic F G₁ G₂ K M cost) (p.1, m, ()) (p, acc, m, xs, ())
  simp only [Env.append] at hw
  dsimp [arithmetic, CryptoOp.price] at hw ⊢
  simp only [weightedSumBody, Expr.run, Var.get, Var.depth, hw]
  congr 1
  omega

omit [DecidableEq F] in
private theorem foldl_weightedSum {I : Type} (w : I → F) (xs : List (I × F)) (acc : F) :
    xs.foldl (fun a p => a + p.2 * w p.1) acc = acc + (xs.map (fun p => p.2 * w p.1)).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons p xs ih =>
      simpa only [List.foldl_cons, List.map_cons, List.sum_cons, add_assoc] using
        (ih (acc + p.2 * w p.1))

theorem weightedSum_value (cost : PrimitiveCosts)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (xs : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) :
    ((weightedSum weight).run (arithmetic F G₁ G₂ K M cost) (m, xs, ())).value =
      (xs.map fun p => p.2 * (weight.run (arithmetic F G₁ G₂ K M cost) (p.1, m, ())).value).sum := by
  change (foldRun
    (fun p acc => (weightedSumBody weight).run (arithmetic F G₁ G₂ K M cost) (p, acc, m, xs, ()))
    xs 0).value = _
  rw [foldRun_value]
  simp_rw [weightedSumBody_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  simpa only [zero_add] using foldl_weightedSum
    (fun i => (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).value) xs 0

theorem weightedSum_steps_le (cost : PrimitiveCosts)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (xs : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F))
    (cWeight : Nat)
    (hweight : ∀ i, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ cWeight) :
    ((weightedSum weight).run (arithmetic F G₁ G₂ K M cost) (m, xs, ())).steps ≤
      xs.length * (cWeight + 2 * cost.field + 27) + cost.field + 6 := by
  have h := foldRun_steps_le
    (fun p acc => (weightedSumBody weight).run (arithmetic F G₁ G₂ K M cost) (p, acc, m, xs, ()))
    (cWeight + 2 * cost.field + 24) (by
      intro p acc
      rw [weightedSumBody_run]
      dsimp
      exact Nat.add_le_add_right (Nat.add_le_add_right (hweight p.1) _) _) xs 0
  change 2 + (1 + cost.field + 1) + (foldRun
    (fun p acc => (weightedSumBody weight).run (arithmetic F G₁ G₂ K M cost) (p, acc, m, xs, ()))
    xs 0).steps + 1 ≤ _
  nlinarith

end Signatures.Runtime.AGM
