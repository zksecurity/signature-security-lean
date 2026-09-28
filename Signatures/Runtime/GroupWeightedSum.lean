import Signatures.Runtime.WeightedSum
import Signatures.Runtime.TableRefinement

/-! Executed group-valued linear combinations for the bad-branch signing simulator. -/

namespace Signatures.Runtime.AGM

variable {indexTy messageTy : Ty CryptoAtom}

def groupWeightedBody (weight : Expr CryptoOp [indexTy, messageTy] scalar) :
    Expr CryptoOp [.pair indexTy point₁, point₁, messageTy, .list (.pair indexTy point₁)] point₁ :=
  .letE (.var (.there (.there .here)))
    (.letE (.fst (.var (.there .here)))
      (.letE (weight.weakenTail
        [.pair indexTy point₁, point₁, messageTy, .list (.pair indexTy point₁)])
        (.op .add₁ (.pair (.var (.there (.there (.there (.there .here)))))
          (.op .scale₁ (.pair (.var .here) (.snd (.var (.there (.there (.there .here)))))))))))

def groupWeightedSum (weight : Expr CryptoOp [indexTy, messageTy] scalar) :
    Expr CryptoOp [messageTy, .list (.pair indexTy point₁)] point₁ :=
  .fold (.var (.there .here)) (.op .zero₁ .unit) (groupWeightedBody weight)

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem groupWeightedBody_run (cost : PrimitiveCosts)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (p : indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁) (acc : G₁)
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (xs : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) :
    (groupWeightedBody weight).run (arithmetic F G₁ G₂ K M cost) (p, acc, m, xs, ()) =
      let r := weight.run (arithmetic F G₁ G₂ K M cost) (p.1, m, ())
      ⟨acc + r.value • p.2, r.steps + cost.scalar₁ + cost.group + 24⟩ := by
  have hw := weight.weakenTail_run
    (Δ := [.pair indexTy point₁, point₁, messageTy, .list (.pair indexTy point₁)])
    (arithmetic F G₁ G₂ K M cost) (p.1, m, ()) (p, acc, m, xs, ())
  simp only [Env.append] at hw
  dsimp [arithmetic, CryptoOp.price] at hw ⊢
  simp only [groupWeightedBody, Expr.run, Var.get, Var.depth, hw]
  congr 1
  omega

omit [DecidableEq F] [DecidableEq G₁] in
private theorem foldl_groupWeighted {I : Type} (w : I → F) (xs : List (I × G₁)) (acc : G₁) :
    xs.foldl (fun a p => a + w p.1 • p.2) acc = acc + (xs.map (fun p => w p.1 • p.2)).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons p xs ih =>
      simpa only [List.foldl_cons, List.map_cons, List.sum_cons, add_assoc] using
        (ih (acc + w p.1 • p.2))

theorem groupWeightedSum_value (cost : PrimitiveCosts)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (xs : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) :
    ((groupWeightedSum weight).run (arithmetic F G₁ G₂ K M cost) (m, xs, ())).value =
      (xs.map fun p => (weight.run (arithmetic F G₁ G₂ K M cost) (p.1, m, ())).value • p.2).sum := by
  change (foldRun
    (fun p acc => (groupWeightedBody weight).run (arithmetic F G₁ G₂ K M cost) (p, acc, m, xs, ()))
    xs 0).value = _
  rw [foldRun_value]
  simp_rw [groupWeightedBody_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  simpa only [zero_add] using foldl_groupWeighted
    (fun i => (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).value) xs 0

theorem groupWeightedSum_steps_le (cost : PrimitiveCosts)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (xs : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁))
    (cWeight : Nat)
    (hweight : ∀ i, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ cWeight) :
    ((groupWeightedSum weight).run (arithmetic F G₁ G₂ K M cost) (m, xs, ())).steps ≤
      xs.length * (cWeight + cost.scalar₁ + cost.group + 27) + cost.group + 6 := by
  have h := foldRun_steps_le
    (fun p acc => (groupWeightedBody weight).run (arithmetic F G₁ G₂ K M cost) (p, acc, m, xs, ()))
    (cWeight + cost.scalar₁ + cost.group + 24) (by
      intro p acc
      rw [groupWeightedBody_run]
      dsimp
      have := hweight p.1
      omega) xs 0
  change 2 + (1 + cost.group + 1) + (foldRun
    (fun p acc => (groupWeightedBody weight).run (arithmetic F G₁ G₂ K M cost) (p, acc, m, xs, ()))
    xs 0).steps + 1 ≤ _
  nlinarith

theorem groupWeightedSum_native {ι : Type} [Fintype ι]
    (cost : PrimitiveCosts) (encode : ι → indexTy.Value (cryptoBase F G₁ G₂ K M))
    (H : ι → G₁) (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M)) :
    ((groupWeightedSum weight).run (arithmetic F G₁ G₂ K M cost)
      (m, canonicalKeys (fun i => (encode i, H i)), ())).value =
      ∑ i, (weight.run (arithmetic F G₁ G₂ K M cost) (encode i, m, ())).value • H i := by
  rw [groupWeightedSum_value, canonicalKeys_sum]

end Signatures.Runtime.AGM
