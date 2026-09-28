import Signatures.Runtime.ExtractionWeights
import Signatures.Runtime.TableRefinement
import Mathlib.Data.List.Indexes

/-! Final field arithmetic for both AGM branches, over prepared transcript coefficient rows.
Every finite-table sum is an executed fold of first-order syntax. Transcript preparation is
charged separately by `tokenRows`; no whole-extractor runtime premise is used here. -/

namespace Signatures.Runtime.AGM

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
private def v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))
private def v4 {a b c d e Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: Γ) e :=
  .var (.there (.there (.there (.there .here))))
private def v5 {a b c d e f Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: Γ) f :=
  .var (.there (.there (.there (.there (.there .here)))))

variable {indexTy messageTy : Ty CryptoAtom}

def goodCore (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) :
    Expr CryptoOp [tableTy indexTy, scalar, tokenRowsTy indexTy, denominatorData messageTy] scalar :=
  .letE (.letE v0 (.letE v3 ((weightedSum (baseCoefficient eq)).weakenTail
      [tableTy indexTy, scalar, tokenRowsTy indexTy, denominatorData messageTy])))
    (.letE (.letE v1 (.letE v5 ((weightedSum (denominatorWeight weight)).weakenTail
      [scalar, tableTy indexTy, scalar, tokenRowsTy indexTy, denominatorData messageTy])))
      (.op .div (.pair (.op .add (.pair v3 v1)) v0)))

def badCore (weight : Expr CryptoOp [indexTy, messageTy] scalar) :
    Expr CryptoOp [tableTy indexTy, tableTy indexTy, denominatorData messageTy] scalar :=
  .letE (.letE v0 (.letE v3 ((weightedSum (denominatorWeight weight)).weakenTail
      [tableTy indexTy, tableTy indexTy, denominatorData messageTy])))
    (.letE (.letE v2 (.letE v4 ((weightedSum (denominatorWeight weight)).weakenTail
      [scalar, tableTy indexTy, tableTy indexTy, denominatorData messageTy])))
      (.op .div (.pair (.op .neg v0) v1)))

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem goodCore_run (cost : PrimitiveCosts)
    (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (rho : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (beta : F)
    (hs : (tokenRowsTy indexTy).Value (cryptoBase F G₁ G₂ K M))
    (ds : (denominatorData messageTy).Value (cryptoBase F G₁ G₂ K M)) :
    (goodCore eq weight).run (arithmetic F G₁ G₂ K M cost) (rho, beta, hs, ds, ()) =
      let c := (weightedSum (baseCoefficient eq)).run (arithmetic F G₁ G₂ K M cost) (hs, rho, ())
      let d := (weightedSum (denominatorWeight weight)).run (arithmetic F G₁ G₂ K M cost) (ds, rho, ())
      ⟨(beta + c.value) / d.value, c.steps + d.steps + cost.field + cost.division + 30⟩ := by
  have hc := (weightedSum (baseCoefficient eq)).weakenTail_run
    (Δ := [tableTy indexTy, scalar, tokenRowsTy indexTy, denominatorData messageTy])
    (arithmetic F G₁ G₂ K M cost) (hs, rho, ()) (rho, beta, hs, ds, ())
  have hd := (weightedSum (denominatorWeight weight)).weakenTail_run
    (Δ := [scalar, tableTy indexTy, scalar, tokenRowsTy indexTy, denominatorData messageTy])
    (arithmetic F G₁ G₂ K M cost) (ds, rho, ())
    (((weightedSum (baseCoefficient eq)).run (arithmetic F G₁ G₂ K M cost) (hs, rho, ())).value,
      rho, beta, hs, ds, ())
  simp only [Env.append] at hc hd
  dsimp [arithmetic, CryptoOp.price] at hc hd ⊢
  simp only [goodCore, Expr.run, v0, v1, v3, v5, Var.get, Var.depth, hc, hd]
  congr 1
  omega

theorem badCore_run (cost : PrimitiveCosts)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (a b : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F))
    (ds : (denominatorData messageTy).Value (cryptoBase F G₁ G₂ K M)) :
    (badCore weight).run (arithmetic F G₁ G₂ K M cost) (a, b, ds, ()) =
      let ar := (weightedSum (denominatorWeight weight)).run (arithmetic F G₁ G₂ K M cost) (ds, a, ())
      let br := (weightedSum (denominatorWeight weight)).run (arithmetic F G₁ G₂ K M cost) (ds, b, ())
      ⟨-br.value / ar.value, ar.steps + br.steps + cost.field + cost.division + 25⟩ := by
  have ha := (weightedSum (denominatorWeight weight)).weakenTail_run
    (Δ := [tableTy indexTy, tableTy indexTy, denominatorData messageTy])
    (arithmetic F G₁ G₂ K M cost) (ds, a, ()) (a, b, ds, ())
  have hb := (weightedSum (denominatorWeight weight)).weakenTail_run
    (Δ := [scalar, tableTy indexTy, tableTy indexTy, denominatorData messageTy])
    (arithmetic F G₁ G₂ K M cost) (ds, b, ())
    (((weightedSum (denominatorWeight weight)).run (arithmetic F G₁ G₂ K M cost) (ds, a, ())).value,
      a, b, ds, ())
  simp only [Env.append] at ha hb
  dsimp [arithmetic, CryptoOp.price] at ha hb ⊢
  simp only [badCore, Expr.run, v0, v1, v2, v3, v4, Var.get, Var.depth, ha, hb]
  congr 1
  omega

def goodCoreBound (cost : PrimitiveCosts) (n h s e w : Nat) : Nat :=
  n * (baseCoefficientBound cost h e + denominatorWeightBound cost s w + 4 * cost.field + 54) +
    3 * cost.field + cost.division + 42

def badCoreBound (cost : PrimitiveCosts) (na nb s w : Nat) : Nat :=
  (na + nb) * (denominatorWeightBound cost s w + 2 * cost.field + 27) +
    3 * cost.field + cost.division + 37

theorem goodCore_steps_le (cost : PrimitiveCosts)
    (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (e w : Nat)
    (heq : ∀ x y, (eq.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤ e)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ w)
    (rho : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (beta : F)
    (hs : (tokenRowsTy indexTy).Value (cryptoBase F G₁ G₂ K M))
    (ds : (denominatorData messageTy).Value (cryptoBase F G₁ G₂ K M)) :
    ((goodCore eq weight).run (arithmetic F G₁ G₂ K M cost) (rho, beta, hs, ds, ())).steps ≤
      goodCoreBound cost rho.length hs.length ds.2.length e w := by
  rw [goodCore_run]
  have hc := weightedSum_steps_le cost (baseCoefficient eq) hs rho
    (baseCoefficientBound cost hs.length e) (fun i => baseCoefficient_steps_le cost eq e heq i hs)
  have hd := weightedSum_steps_le cost (denominatorWeight weight) ds rho
    (denominatorWeightBound cost ds.2.length w)
    (fun i => denominatorWeight_steps_le cost weight w hw i ds.1 ds.2)
  dsimp [goodCoreBound]
  nlinarith

theorem badCore_steps_le (cost : PrimitiveCosts)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (w : Nat)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ w)
    (a b : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F))
    (ds : (denominatorData messageTy).Value (cryptoBase F G₁ G₂ K M)) :
    ((badCore weight).run (arithmetic F G₁ G₂ K M cost) (a, b, ds, ())).steps ≤
      badCoreBound cost a.length b.length ds.2.length w := by
  rw [badCore_run]
  have ha := weightedSum_steps_le cost (denominatorWeight weight) ds a
    (denominatorWeightBound cost ds.2.length w)
    (fun i => denominatorWeight_steps_le cost weight w hw i ds.1 ds.2)
  have hb := weightedSum_steps_le cost (denominatorWeight weight) ds b
    (denominatorWeightBound cost ds.2.length w)
    (fun i => denominatorWeight_steps_le cost weight w hw i ds.1 ds.2)
  dsimp [badCoreBound]
  nlinarith

omit [DecidableEq F] in
theorem weighted_denominator_sum {I D P : Type} [Fintype I]
    (w : I → D → F) (rho : I → F) (m : D) (coeff : List F) (tr : List (D × P)) :
    (∑ i, rho i * (w i m - (tr.mapIdx fun n p => Model.LazyAGM.tokenCoeff coeff n * w i p.1).sum)) =
      (∑ i, rho i * w i m) -
        (tr.mapIdx fun n p => Model.LazyAGM.tokenCoeff coeff n * (∑ i, rho i * w i p.1)).sum := by
  simp only [mul_sub, Finset.sum_sub_distrib, List.mapIdx_eq_ofFn, List.sum_ofFn, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem goodCore_native {I : Type} [Fintype I]
    [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
    (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (encode : I → indexTy.Value (cryptoBase F G₁ G₂ K M)) (rho : I → F)
    (out : Model.LazyAGM.Output F (messageTy.Value (cryptoBase F G₁ G₂ K M)))
    (tr : Model.LazyAGM.Transcript (indexTy.Value (cryptoBase F G₁ G₂ K M))
      (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁) :
    ((goodCore eq weight).run (arithmetic F G₁ G₂ K M cost)
      (canonicalKeys (fun j => (encode j, rho j)), out.β,
        tr.1.mapIdx (fun n p => (p, Model.LazyAGM.tokenCoeff out.γ n)),
        (out.mstar, tr.2.mapIdx (fun n p => (p, Model.LazyAGM.tokenCoeff out.ξ n))), ())).value =
      (out.β + ∑ j, Model.LazyAGM.baseCoeff out.γ tr.1 (encode j) * rho j) /
        ((∑ j, rho j * (weight.run (arithmetic F G₁ G₂ K M cost) (encode j, out.mstar, ())).value) -
          (tr.2.mapIdx fun n p => Model.LazyAGM.tokenCoeff out.ξ n *
            (∑ j, rho j * (weight.run (arithmetic F G₁ G₂ K M cost) (encode j, p.1, ())).value)).sum) := by
  rw [goodCore_run]
  change (out.β + ((weightedSum (baseCoefficient eq)).run (arithmetic F G₁ G₂ K M cost)
    (tr.1.mapIdx (fun n p => (p, Model.LazyAGM.tokenCoeff out.γ n)),
      canonicalKeys (fun j => (encode j, rho j)), ())).value) /
    ((weightedSum (denominatorWeight weight)).run (arithmetic F G₁ G₂ K M cost)
      ((out.mstar, tr.2.mapIdx (fun n p => (p, Model.LazyAGM.tokenCoeff out.ξ n))),
        canonicalKeys (fun j => (encode j, rho j)), ())).value = _
  rw [weightedSum_value, weightedSum_value]
  simp only [canonicalKeys_sum]
  simp_rw [baseCoefficient_native (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost eq heq,
    denominatorWeight_native (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  apply congrArg₂ (fun x y : F => x / y)
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  · exact weighted_denominator_sum
      (fun j m => (weight.run (arithmetic F G₁ G₂ K M cost) (encode j, m, ())).value)
      rho out.mstar out.ξ tr.2

theorem badCore_native {I : Type} [Fintype I]
    (cost : PrimitiveCosts) (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (encode : I → indexTy.Value (cryptoBase F G₁ G₂ K M)) (a b : I → F)
    (out : Model.LazyAGM.Output F (messageTy.Value (cryptoBase F G₁ G₂ K M)))
    (tr : Model.LazyAGM.Transcript (indexTy.Value (cryptoBase F G₁ G₂ K M))
      (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁) :
    ((badCore weight).run (arithmetic F G₁ G₂ K M cost)
      (canonicalKeys (fun j => (encode j, a j)), canonicalKeys (fun j => (encode j, b j)),
        (out.mstar, tr.2.mapIdx (fun n p => (p, Model.LazyAGM.tokenCoeff out.ξ n))), ())).value =
      -(∑ j, Model.LazyAGM.denominatorCoeff
        (fun i m => (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).value) out tr (encode j) * b j) /
      (∑ j, Model.LazyAGM.denominatorCoeff
        (fun i m => (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).value) out tr (encode j) * a j) := by
  rw [badCore_run]
  change -((weightedSum (denominatorWeight weight)).run (arithmetic F G₁ G₂ K M cost)
    ((out.mstar, tr.2.mapIdx (fun n p => (p, Model.LazyAGM.tokenCoeff out.ξ n))),
      canonicalKeys (fun j => (encode j, b j)), ())).value /
    ((weightedSum (denominatorWeight weight)).run (arithmetic F G₁ G₂ K M cost)
      ((out.mstar, tr.2.mapIdx (fun n p => (p, Model.LazyAGM.tokenCoeff out.ξ n))),
        canonicalKeys (fun j => (encode j, a j)), ())).value = _
  rw [weightedSum_value, weightedSum_value]
  simp only [canonicalKeys_sum]
  simp_rw [denominatorWeight_native (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  apply congrArg₂ (fun x y : F => x / y)
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _

end Signatures.Runtime.AGM
