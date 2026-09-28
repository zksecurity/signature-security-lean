import Signatures.Runtime.TokenCoefficients
import Signatures.Runtime.WeightedSum

/-! Compiled scalar weights used by the final AGM extractors. Both query coefficients and
denominator coefficients are computed from explicit transcript rows, not oracle opcodes. -/

namespace Signatures.Runtime.AGM

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
private def v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))
private def v4 {a b c d e Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: Γ) e :=
  .var (.there (.there (.there (.there .here))))

variable {indexTy messageTy : Ty CryptoAtom}

def tokenWeight (weight : Expr CryptoOp [indexTy, messageTy] scalar) :
    Expr CryptoOp [tokenTy messageTy, indexTy] scalar :=
  .letE (.fst v0) (.letE v2 (weight.weakenTail [tokenTy messageTy, indexTy]))

def baseIndicator (eq : Expr CryptoOp [indexTy, indexTy] .bool) :
    Expr CryptoOp [tokenTy indexTy, indexTy] scalar :=
  .letE v1 (.letE (.fst v1)
    (.branch (eq.weakenTail [tokenTy indexTy, indexTy]) (.op .one .unit) (.op .zero .unit)))

def baseCoefficient (eq : Expr CryptoOp [indexTy, indexTy] .bool) :
    Expr CryptoOp [indexTy, tokenRowsTy indexTy] scalar := weightedSum (baseIndicator eq)

abbrev denominatorData (messageTy : Ty CryptoAtom) : Ty CryptoAtom :=
  .pair messageTy (tokenRowsTy messageTy)

def denominatorWeight (weight : Expr CryptoOp [indexTy, messageTy] scalar) :
    Expr CryptoOp [indexTy, denominatorData messageTy] scalar :=
  .letE (.snd v1)
    (.letE v1
      (.letE ((weightedSum (tokenWeight weight)).weakenTail [indexTy, denominatorData messageTy])
        (.letE (.fst v4)
          (.letE v4
            (.letE (weight.weakenTail
              [scalar, indexTy, tokenRowsTy messageTy, indexTy, denominatorData messageTy])
              (.op .sub (.pair v0 v3)))))))

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem tokenWeight_run (cost : PrimitiveCosts)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (p : messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁)
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M)) :
    (tokenWeight weight).run (arithmetic F G₁ G₂ K M cost) (p, i, ()) =
      let r := weight.run (arithmetic F G₁ G₂ K M cost) (i, p.1, ())
      ⟨r.value, r.steps + 7⟩ := by
  have h := weight.weakenTail_run (Δ := [tokenTy messageTy, indexTy])
    (arithmetic F G₁ G₂ K M cost) (i, p.1, ()) (p, i, ())
  simp only [Env.append] at h
  simp only [tokenWeight, Expr.run, v0, v2, Var.get, Var.depth, h]
  congr 1
  omega

theorem baseIndicator_run (cost : PrimitiveCosts)
    (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (p : indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁)
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M)) :
    (baseIndicator eq).run (arithmetic F G₁ G₂ K M cost) (p, i, ()) =
      let r := eq.run (arithmetic F G₁ G₂ K M cost) (p.1, i, ())
      ⟨if r.value then 1 else 0, r.steps + cost.field + 10⟩ := by
  have h := eq.weakenTail_run (Δ := [tokenTy indexTy, indexTy])
    (arithmetic F G₁ G₂ K M cost) (p.1, i, ()) (p, i, ())
  simp only [Env.append] at h
  dsimp [arithmetic, CryptoOp.price] at h ⊢
  simp only [baseIndicator, Expr.run, v1, Var.get, Var.depth, h]
  split <;> congr 1 <;> dsimp <;> omega

theorem denominatorWeight_run (cost : PrimitiveCosts)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M))
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (rows : List ((messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁) × F)) :
    (denominatorWeight weight).run (arithmetic F G₁ G₂ K M cost) (i, (m, rows), ()) =
      let s := (weightedSum (tokenWeight weight)).run (arithmetic F G₁ G₂ K M cost) (i, rows, ())
      let w := weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())
      ⟨w.value - s.value, s.steps + w.steps + cost.field + 29⟩ := by
  have hs := (weightedSum (tokenWeight weight)).weakenTail_run
    (Δ := [indexTy, denominatorData messageTy]) (arithmetic F G₁ G₂ K M cost)
    (i, rows, ()) (i, (m, rows), ())
  have hw := weight.weakenTail_run
    (Δ := [scalar, indexTy, tokenRowsTy messageTy, indexTy, denominatorData messageTy])
    (arithmetic F G₁ G₂ K M cost) (i, m, ())
    (((weightedSum (tokenWeight weight)).run (arithmetic F G₁ G₂ K M cost) (i, rows, ())).value,
      i, rows, i, (m, rows), ())
  simp only [Env.append] at hs hw
  dsimp [arithmetic, CryptoOp.price] at hs hw ⊢
  simp only [denominatorWeight, Expr.run, v0, v1, v3, v4, Var.get, Var.depth, hs, hw]
  congr 1
  omega

def denominatorWeightBound (cost : PrimitiveCosts) (n w : Nat) : Nat :=
  n * (w + 2 * cost.field + 34) + w + 2 * cost.field + 35

theorem denominatorWeight_steps_le (cost : PrimitiveCosts)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (w : Nat)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ w)
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M))
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (rows : List ((messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁) × F)) :
    ((denominatorWeight weight).run (arithmetic F G₁ G₂ K M cost) (i, (m, rows), ())).steps ≤
      denominatorWeightBound cost rows.length w := by
  rw [denominatorWeight_run]
  have hs := weightedSum_steps_le cost (tokenWeight weight) i rows (w + 7) (by
    intro p
    rw [tokenWeight_run]
    exact Nat.add_le_add_right (hw i p.1) 7)
  have hm := hw i m
  dsimp [denominatorWeightBound] at *
  nlinarith

theorem baseCoefficient_value (cost : PrimitiveCosts)
    [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
    (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M))
    (rows : List ((indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁) × F)) :
    ((baseCoefficient eq).run (arithmetic F G₁ G₂ K M cost) (i, rows, ())).value =
      (rows.map fun p => if p.1.1 = i then p.2 else 0).sum := by
  rw [baseCoefficient, weightedSum_value]
  simp only [baseIndicator_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  simp only [Expr.run_value, heq, decide_eq_true_eq, mul_ite, mul_one, mul_zero]

def baseCoefficientBound (cost : PrimitiveCosts) (n e : Nat) : Nat :=
  n * (e + 3 * cost.field + 37) + cost.field + 6

theorem baseCoefficient_steps_le (cost : PrimitiveCosts)
    (eq : Expr CryptoOp [indexTy, indexTy] .bool) (e : Nat)
    (heq : ∀ x y, (eq.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤ e)
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M))
    (rows : List ((indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁) × F)) :
    ((baseCoefficient eq).run (arithmetic F G₁ G₂ K M cost) (i, rows, ())).steps ≤
      baseCoefficientBound cost rows.length e := by
  have h := weightedSum_steps_le cost (baseIndicator eq) i rows (e + cost.field + 10) (by
    intro p
    rw [baseIndicator_run]
    exact Nat.add_le_add_right (Nat.add_le_add_right (heq p.1 i) _) _)
  dsimp [baseCoefficient, baseCoefficientBound]
  nlinarith

theorem denominatorWeight_value (cost : PrimitiveCosts)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M))
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (rows : List ((messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁) × F)) :
    ((denominatorWeight weight).run (arithmetic F G₁ G₂ K M cost) (i, (m, rows), ())).value =
      (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).value -
        (rows.map fun p => p.2 * (weight.run (arithmetic F G₁ G₂ K M cost) (i, p.1.1, ())).value).sum := by
  rw [denominatorWeight_run]
  dsimp only
  rw [weightedSum_value]
  simp only [tokenWeight_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]

theorem baseCoefficient_native (cost : PrimitiveCosts)
    [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
    (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M))
    (tr : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F) :
    ((baseCoefficient eq).run (arithmetic F G₁ G₂ K M cost)
      (i, tr.mapIdx (fun n p => (p, Model.LazyAGM.tokenCoeff coeff n)), ())).value =
      Model.LazyAGM.baseCoeff coeff tr i := by
  rw [baseCoefficient_value _ _ heq]
  simp [Model.LazyAGM.baseCoeff, List.mapIdx_eq_zipIdx_map, List.map_map, Function.comp_def]

theorem denominatorWeight_native (cost : PrimitiveCosts)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M))
    (out : Model.LazyAGM.Output F (messageTy.Value (cryptoBase F G₁ G₂ K M)))
    (tr : Model.LazyAGM.Transcript (indexTy.Value (cryptoBase F G₁ G₂ K M))
      (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁) :
    ((denominatorWeight weight).run (arithmetic F G₁ G₂ K M cost)
      (i, (out.mstar, tr.2.mapIdx (fun n p => (p, Model.LazyAGM.tokenCoeff out.ξ n))), ())).value =
      Model.LazyAGM.denominatorCoeff
        (fun j m => (weight.run (arithmetic F G₁ G₂ K M cost) (j, m, ())).value) out tr i := by
  rw [denominatorWeight_value]
  simp [Model.LazyAGM.denominatorCoeff, List.mapIdx_eq_zipIdx_map, List.map_map, Function.comp_def]

end Signatures.Runtime.AGM
