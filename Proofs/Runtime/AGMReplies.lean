import Proofs.Runtime.GroupWeightedSum
import Proofs.Runtime.LookupExpr

/-! Actual reply expressions for the good and bad AGM reductions. Configurations contain
private scalar/group tables; neither hash nor signing is a primitive instruction. -/

namespace Signatures.Runtime.AGM

abbrev goodConfig (indexTy : Ty CryptoAtom) : Ty CryptoAtom :=
  .pair point₁ (.pair point₁ (tableTy indexTy))

abbrev badConfig (indexTy : Ty CryptoAtom) : Ty CryptoAtom :=
  .pair scalar (.list (.pair indexTy point₁))

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
private def v4 {a b c d e Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: Γ) e :=
  .var (.there (.there (.there (.there .here))))
private def v5 {a b c d e f Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: Γ) f :=
  .var (.there (.there (.there (.there (.there .here)))))

variable {indexTy messageTy : Ty CryptoAtom}

def goodHash (eq : Expr CryptoOp [indexTy, indexTy] .bool) :
    Expr CryptoOp [indexTy, goodConfig indexTy] point₁ :=
  .letE (.snd (.snd v1))
    (.letE (.op .zero .unit)
      (.letE v2
        (.letE ((lookupExpr (val := scalar) eq).weakenTail [indexTy, goodConfig indexTy])
          (.op .scale₁ (.pair (.snd v0) (.fst v5))))))

def goodSign (weight : Expr CryptoOp [indexTy, messageTy] scalar) :
    Expr CryptoOp [messageTy, goodConfig indexTy] point₁ :=
  .letE (.snd (.snd v1))
    (.letE v1
      (.letE ((weightedSum weight).weakenTail [messageTy, goodConfig indexTy])
        (.op .scale₁ (.pair v0 (.fst (.snd v4))))))

def badHash (eq : Expr CryptoOp [indexTy, indexTy] .bool) :
    Expr CryptoOp [indexTy, badConfig indexTy] point₁ :=
  .letE (.snd v1)
    (.letE (.op .zero₁ .unit)
      (.letE v2
        (.letE ((lookupExpr (val := point₁) eq).weakenTail [indexTy, badConfig indexTy]) (.snd v0))))

def badSign (weight : Expr CryptoOp [indexTy, messageTy] scalar) :
    Expr CryptoOp [messageTy, badConfig indexTy] point₁ :=
  .letE (.snd v1)
    (.letE v1
      (.letE ((groupWeightedSum weight).weakenTail [messageTy, badConfig indexTy])
        (.op .scale₁ (.pair (.fst v4) v0))))

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem goodHash_run (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M)) (g X : G₁)
    (rho : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) :
    (goodHash eq).run (arithmetic F G₁ G₂ K M cost) (i, (g, X, rho), ()) =
      let r := (lookupExpr (val := scalar) eq).run (arithmetic F G₁ G₂ K M cost) (i, 0, rho, ())
      ⟨r.value.2 • g, r.steps + cost.field + cost.scalar₁ + 24⟩ := by
  have h := (lookupExpr (val := scalar) eq).weakenTail_run
    (Δ := [indexTy, goodConfig indexTy]) (arithmetic F G₁ G₂ K M cost)
    (i, 0, rho, ()) (i, (g, X, rho), ())
  simp only [Env.append] at h
  dsimp [arithmetic, CryptoOp.price] at h ⊢
  simp only [goodHash, Expr.run, v0, v1, v2, v5, Var.get, Var.depth, h]
  congr 1
  omega

theorem goodSign_run (cost : PrimitiveCosts) (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M)) (g X : G₁)
    (rho : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) :
    (goodSign weight).run (arithmetic F G₁ G₂ K M cost) (m, (g, X, rho), ()) =
      let r := (weightedSum weight).run (arithmetic F G₁ G₂ K M cost) (m, rho, ())
      ⟨r.value • X, r.steps + cost.scalar₁ + 19⟩ := by
  have h := (weightedSum weight).weakenTail_run
    (Δ := [messageTy, goodConfig indexTy]) (arithmetic F G₁ G₂ K M cost)
    (m, rho, ()) (m, (g, X, rho), ())
  simp only [Env.append] at h
  dsimp [arithmetic, CryptoOp.price] at h ⊢
  simp only [goodSign, Expr.run, v0, v1, v4, Var.get, Var.depth, h]
  congr 1
  omega

theorem badHash_run (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M)) (kappa : F)
    (H : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) :
    (badHash eq).run (arithmetic F G₁ G₂ K M cost) (i, (kappa, H), ()) =
      let r := (lookupExpr (val := point₁) eq).run (arithmetic F G₁ G₂ K M cost) (i, 0, H, ())
      ⟨r.value.2, r.steps + cost.group + 14⟩ := by
  have h := (lookupExpr (val := point₁) eq).weakenTail_run
    (Δ := [indexTy, badConfig indexTy]) (arithmetic F G₁ G₂ K M cost)
    (i, 0, H, ()) (i, (kappa, H), ())
  simp only [Env.append] at h
  dsimp [arithmetic, CryptoOp.price] at h ⊢
  simp only [badHash, Expr.run, v0, v1, v2, Var.get, Var.depth, h]
  congr 1
  omega

theorem badSign_run (cost : PrimitiveCosts) (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M)) (kappa : F)
    (H : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) :
    (badSign weight).run (arithmetic F G₁ G₂ K M cost) (m, (kappa, H), ()) =
      let r := (groupWeightedSum weight).run (arithmetic F G₁ G₂ K M cost) (m, H, ())
      ⟨kappa • r.value, r.steps + cost.scalar₁ + 17⟩ := by
  have h := (groupWeightedSum weight).weakenTail_run
    (Δ := [messageTy, badConfig indexTy]) (arithmetic F G₁ G₂ K M cost)
    (m, H, ()) (m, (kappa, H), ())
  simp only [Env.append] at h
  dsimp [arithmetic, CryptoOp.price] at h ⊢
  simp only [badSign, Expr.run, v0, v1, v4, Var.get, Var.depth, h]
  congr 1
  omega

def goodHashBound (cost : PrimitiveCosts) (n cEq : Nat) : Nat :=
  n * (cEq + 22) + cost.field + cost.scalar₁ + 33

def goodSignBound (cost : PrimitiveCosts) (n cWeight : Nat) : Nat :=
  n * (cWeight + 2 * cost.field + 27) + cost.field + cost.scalar₁ + 25

def badHashBound (cost : PrimitiveCosts) (n cEq : Nat) : Nat :=
  n * (cEq + 22) + cost.group + 23

def badSignBound (cost : PrimitiveCosts) (n cWeight : Nat) : Nat :=
  n * (cWeight + cost.scalar₁ + cost.group + 27) + cost.group + cost.scalar₁ + 23

theorem goodHash_steps_le (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (cEq : Nat) (heq : ∀ x y, (eq.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤ cEq)
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M)) (g X : G₁)
    (rho : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) :
    ((goodHash eq).run (arithmetic F G₁ G₂ K M cost) (i, (g, X, rho), ())).steps ≤
      goodHashBound cost rho.length cEq := by
  rw [goodHash_run]
  have h := lookupExpr_steps_le (val := scalar) (arithmetic F G₁ G₂ K M cost) eq cEq heq i 0 rho
  dsimp [goodHashBound]
  omega

theorem goodSign_steps_le (cost : PrimitiveCosts) (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (cWeight : Nat) (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (hw : ∀ i, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ cWeight)
    (g X : G₁) (rho : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) :
    ((goodSign weight).run (arithmetic F G₁ G₂ K M cost) (m, (g, X, rho), ())).steps ≤
      goodSignBound cost rho.length cWeight := by
  rw [goodSign_run]
  have h := weightedSum_steps_le cost weight m rho cWeight hw
  dsimp [goodSignBound]
  omega

theorem badHash_steps_le (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (cEq : Nat) (heq : ∀ x y, (eq.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤ cEq)
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M)) (kappa : F)
    (H : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) :
    ((badHash eq).run (arithmetic F G₁ G₂ K M cost) (i, (kappa, H), ())).steps ≤
      badHashBound cost H.length cEq := by
  rw [badHash_run]
  have h := lookupExpr_steps_le (val := point₁) (arithmetic F G₁ G₂ K M cost) eq cEq heq i 0 H
  dsimp [badHashBound]
  omega

theorem badSign_steps_le (cost : PrimitiveCosts) (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (cWeight : Nat) (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (hw : ∀ i, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ cWeight)
    (kappa : F) (H : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) :
    ((badSign weight).run (arithmetic F G₁ G₂ K M cost) (m, (kappa, H), ())).steps ≤
      badSignBound cost H.length cWeight := by
  rw [badSign_run]
  have h := groupWeightedSum_steps_le cost weight m H cWeight hw
  dsimp [badSignBound]
  omega

theorem goodHash_native {ι : Type} [Fintype ι]
    [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
    (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (encode : ι → indexTy.Value (cryptoBase F G₁ G₂ K M)) (hinj : Function.Injective encode)
    (rho : ι → F) (g X : G₁) (i : ι) :
    ((goodHash eq).run (arithmetic F G₁ G₂ K M cost)
      (encode i, (g, X, canonicalKeys fun j => (encode j, rho j)), ())).value = rho i • g := by
  rw [goodHash_run]
  change ((lookupExpr (val := scalar) eq).run (arithmetic F G₁ G₂ K M cost)
    (encode i, (0 : F), canonicalKeys (fun j => (encode j, rho j)), ())).value.2 • g = _
  rw [lookupExpr_value _ _ heq, lookupValue_canonical encode hinj]

theorem goodSign_native {ι : Type} [Fintype ι]
    (cost : PrimitiveCosts) (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (encode : ι → indexTy.Value (cryptoBase F G₁ G₂ K M)) (rho : ι → F)
    (g X : G₁) (m : messageTy.Value (cryptoBase F G₁ G₂ K M)) :
    ((goodSign weight).run (arithmetic F G₁ G₂ K M cost)
      (m, (g, X, canonicalKeys fun j => (encode j, rho j)), ())).value =
      (∑ i, rho i * (weight.run (arithmetic F G₁ G₂ K M cost) (encode i, m, ())).value) • X := by
  rw [goodSign_run]
  change ((weightedSum weight).run (arithmetic F G₁ G₂ K M cost)
    (m, canonicalKeys (fun j => (encode j, rho j)), ())).value • X = _
  rw [weightedSum_value, canonicalKeys_sum]

theorem badHash_native {ι : Type} [Fintype ι]
    [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
    (cost : PrimitiveCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (encode : ι → indexTy.Value (cryptoBase F G₁ G₂ K M)) (hinj : Function.Injective encode)
    (H : ι → G₁) (kappa : F) (i : ι) :
    ((badHash eq).run (arithmetic F G₁ G₂ K M cost)
      (encode i, (kappa, canonicalKeys fun j => (encode j, H j)), ())).value = H i := by
  rw [badHash_run]
  change ((lookupExpr (val := point₁) eq).run (arithmetic F G₁ G₂ K M cost)
    (encode i, (0 : G₁), canonicalKeys (fun j => (encode j, H j)), ())).value.2 = _
  rw [lookupExpr_value _ _ heq, lookupValue_canonical encode hinj]

theorem badSign_native {ι : Type} [Fintype ι]
    (cost : PrimitiveCosts) (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (encode : ι → indexTy.Value (cryptoBase F G₁ G₂ K M)) (H : ι → G₁)
    (kappa : F) (m : messageTy.Value (cryptoBase F G₁ G₂ K M)) :
    ((badSign weight).run (arithmetic F G₁ G₂ K M cost)
      (m, (kappa, canonicalKeys fun j => (encode j, H j)), ())).value =
      kappa • ∑ i, (weight.run (arithmetic F G₁ G₂ K M cost) (encode i, m, ())).value • H i := by
  rw [badSign_run]
  change kappa • ((groupWeightedSum weight).run (arithmetic F G₁ G₂ K M cost)
    (m, canonicalKeys (fun j => (encode j, H j)), ())).value = _
  rw [groupWeightedSum_native]

end Signatures.Runtime.AGM
