import Signatures.Runtime.Arithmetic
import Signatures.Runtime.Index
import Signatures.Runtime.Sampling
import Signatures.Runtime.Weakening

/-! Construct an ordered association list from a fixed key enumeration and sampled scalar
cells. All indexing, allocation, and reversal are executed and charged. Missing cells use
an explicit default; native-sampler uses additionally establish the exact table length. -/

namespace Signatures.Runtime.AGM

variable {indexTy : Ty CryptoAtom}

abbrev tableTy (indexTy : Ty CryptoAtom) : Ty CryptoAtom := .list (.pair indexTy scalar)
abbrev attachState (indexTy : Ty CryptoAtom) : Ty CryptoAtom := .pair .nat (tableTy indexTy)

def attachBody : Expr CryptoOp
    [indexTy, attachState indexTy, scalar, .list indexTy, .list scalar] (attachState indexTy) :=
  .letE (.var (.there (.there (.there (.there .here)))))
    (.letE (.var (.there (.there (.there .here))))
      (.letE (.fst (.var (.there (.there (.there .here)))))
        (.letE ((index (cell := scalar) CryptoOp.natEq CryptoOp.natSub).weakenTail
          [indexTy, attachState indexTy, scalar, .list indexTy, .list scalar])
          (.pair (.op .natAdd (.pair (.var (.there .here)) (.nat 1)))
            (.cons (.pair (.var (.there (.there (.there (.there .here))))) (.var .here))
              (.snd (.var (.there (.there (.there (.there (.there .here))))))))))))

def attachFold : Expr CryptoOp [scalar, .list indexTy, .list scalar] (attachState indexTy) :=
  .fold (.var (.there .here)) (.pair (.nat 0) .nil) attachBody

def attachTable : Expr CryptoOp [scalar, .list indexTy, .list scalar] (tableTy indexTy) :=
  .letE attachFold (.letE (.snd (.var .here)) reverseList)

def attachStep {I V : Type} (default : V) (values : List V)
    (acc : Nat × List (I × V)) (i : I) : Nat × List (I × V) :=
  (acc.1 + 1, (i, (values[acc.1]?).getD default) :: acc.2)

theorem attachStep_fold {I V : Type} (default : V) (values : List V)
    (keys : List I) (n : Nat) (acc : List (I × V)) :
    keys.foldl (attachStep default values) (n, acc) =
      (n + keys.length,
        (keys.mapIdx fun j k => (k, (values[n + j]?).getD default)).reverse ++ acc) := by
  induction keys generalizing n acc with
  | nil => simp
  | cons k keys ih =>
      simp only [List.foldl_cons, attachStep, ih, List.length_cons, List.mapIdx_cons,
        List.reverse_cons, List.append_assoc, List.singleton_append, Nat.add_zero]
      congr 1
      · omega
      · simp only [Nat.add_left_comm, Nat.add_comm]

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem attachBody_run (cost : PrimitiveCosts)
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M))
    (acc : Nat × List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F))
    (default : F) (keys : List (indexTy.Value (cryptoBase F G₁ G₂ K M))) (values : List F) :
    (attachBody (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost)
      (i, acc, default, keys, values, ()) =
      let r := (index (cell := scalar) CryptoOp.natEq CryptoOp.natSub).run
        (arithmetic F G₁ G₂ K M cost) (acc.1, default, values, ())
      ⟨(acc.1 + 1, (i, r.value) :: acc.2), r.steps + cost.natOp + 40⟩ := by
  have hi := (index (cell := scalar) CryptoOp.natEq CryptoOp.natSub).weakenTail_run
    (Δ := [indexTy, attachState indexTy, scalar, .list indexTy, .list scalar])
    (arithmetic F G₁ G₂ K M cost) (acc.1, default, values, ()) (i, acc, default, keys, values, ())
  simp only [Env.append] at hi
  dsimp [arithmetic, CryptoOp.price] at hi ⊢
  simp only [attachBody, Expr.run, Var.get, Var.depth, hi]
  congr 1
  omega

theorem attachBody_value (cost : PrimitiveCosts)
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M))
    (acc : Nat × List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F))
    (default : F) (keys : List (indexTy.Value (cryptoBase F G₁ G₂ K M))) (values : List F) :
    ((attachBody (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost)
      (i, acc, default, keys, values, ())).value = attachStep default values acc i := by
  rw [attachBody_run]
  simp only [Expr.run_value, index_denote (cell := scalar) (arithmetic F G₁ G₂ K M cost)
    CryptoOp.natEq CryptoOp.natSub (fun _ _ => rfl) (fun _ _ => rfl), attachStep]

theorem attachFold_value (cost : PrimitiveCosts)
    (default : F) (keys : List (indexTy.Value (cryptoBase F G₁ G₂ K M))) (values : List F) :
    ((attachFold (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost)
      (default, keys, values, ())).value =
      (keys.length, (keys.mapIdx fun n k => (k, (values[n]?).getD default)).reverse) := by
  change (foldRun
    (fun i acc => attachBody.run (arithmetic F G₁ G₂ K M cost) (i, acc, default, keys, values, ()))
    keys (0, [])).value = _
  rw [foldRun_value]
  simp_rw [attachBody_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  simpa only [Nat.zero_add, List.append_nil] using attachStep_fold default values keys 0 []

theorem attachTable_value (cost : PrimitiveCosts)
    (default : F) (keys : List (indexTy.Value (cryptoBase F G₁ G₂ K M))) (values : List F) :
    ((attachTable (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost)
      (default, keys, values, ())).value =
      keys.mapIdx fun n k => (k, (values[n]?).getD default) := by
  simp only [attachTable, Expr.run]
  rw [attachFold_value]
  simp only [Expr.run_value, reverseList_denote (cell := .pair indexTy scalar)
    (Γ := [attachState indexTy, scalar, .list indexTy, .list scalar]), List.reverse_reverse, Var.get]

theorem attachBody_steps_le (cost : PrimitiveCosts)
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M))
    (acc : Nat × List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F))
    (default : F) (keys : List (indexTy.Value (cryptoBase F G₁ G₂ K M))) (values : List F) :
    ((attachBody (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost)
      (i, acc, default, keys, values, ())).steps ≤
      values.length * (2 * cost.natOp + 26) + cost.natOp + 53 := by
  rw [attachBody_run]
  have hi := index_steps_le (cell := scalar) (arithmetic F G₁ G₂ K M cost)
    CryptoOp.natEq CryptoOp.natSub cost.natOp (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    acc.1 default values
  dsimp
  omega

theorem attachFold_steps_le (cost : PrimitiveCosts)
    (default : F) (keys : List (indexTy.Value (cryptoBase F G₁ G₂ K M))) (values : List F) :
    ((attachFold (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost)
      (default, keys, values, ())).steps ≤
      keys.length * (values.length * (2 * cost.natOp + 26) + cost.natOp + 56) + 7 := by
  have h := foldRun_steps_le
    (fun i acc => attachBody.run (arithmetic F G₁ G₂ K M cost) (i, acc, default, keys, values, ()))
    (values.length * (2 * cost.natOp + 26) + cost.natOp + 53)
    (fun i acc => attachBody_steps_le cost i acc default keys values) keys (0, [])
  change 2 + 3 + (foldRun
    (fun i acc => attachBody.run (arithmetic F G₁ G₂ K M cost) (i, acc, default, keys, values, ()))
    keys (0, [])).steps + 1 ≤ _
  nlinarith

theorem attachTable_steps_le (cost : PrimitiveCosts)
    (default : F) (keys : List (indexTy.Value (cryptoBase F G₁ G₂ K M))) (values : List F) :
    ((attachTable (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost)
      (default, keys, values, ())).steps ≤
      keys.length * (values.length * (2 * cost.natOp + 26) + cost.natOp + 63) + 15 := by
  have hf := attachFold_steps_le (indexTy := indexTy) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost default keys values
  have hv := attachFold_value (indexTy := indexTy) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost default keys values
  have hr := reverseList_steps_le (cell := .pair indexTy scalar)
    (Γ := [attachState indexTy, scalar, .list indexTy, .list scalar])
    (arithmetic F G₁ G₂ K M cost)
    (keys.mapIdx fun n k => (k, (values[n]?).getD default)).reverse
    ((keys.length, (keys.mapIdx fun n k => (k, (values[n]?).getD default)).reverse),
      default, keys, values, ())
  simp only [List.length_reverse, List.length_mapIdx] at hr
  simp only [attachTable, Expr.run, Var.get, Var.depth, hv]
  nlinarith

end Signatures.Runtime.AGM
