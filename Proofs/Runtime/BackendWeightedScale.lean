import Proofs.Runtime.WeightedCoefficientsSize
import Proofs.Runtime.BackendFoldGrowth
import Proofs.Runtime.BackendExpressionCost

/-! Native cost of scaling and prepending weighted terms. All retained list
frames and every multiplication, constructor and fold fee are charged. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Coefficients

open Terms BackendProgram

universe v w

private def scaleBody {indexTy : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)} :
    Expr CryptoOp (termTy indexTy :: .list (termTy indexTy) :: .list (termTy indexTy) :: scalar :: Γ)
      (.list (termTy indexTy)) :=
  .cons (.pair (.fst (.var .here))
    (.op .mul (.pair (.var (.there (.there (.there .here)))) (.snd (.var .here)))))
    (.var (.there .here))

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead)

include sizes lists mono

private theorem scaleBody_time {indexTy : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (env : Env (cryptoBase F G₁ G₂ K M)
      (termTy indexTy :: .list (termTy indexTy) :: .list (termTy indexTy) :: scalar :: Γ))
    (width mulTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env
      (termTy indexTy :: .list (termTy indexTy) :: .list (termTy indexTy) :: scalar :: Γ)) env ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hm : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound scaleBody).time env ≤ mulTime + 64 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcons := @lists.cons_le
  have hfield := hf (env.2.2.2.1 * env.1.2)
  have hmul := hm env.2.2.2.1 env.1.2
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  have hmulValue : ∀ x y : F, (arithmetic F G₁ G₂ K M cost).execute .mul (x, y) = x * y :=
    fun _ _ => rfl
  dsimp only [scaleBody, termTy, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.consBound, Expr.denote, Var.get,
    LanguageRepresentation.env, LanguageRepresentation.ty] at *
  simp only [hmulValue] at *
  grind only

def scaleWidth (width cap : Nat) : Nat := (16 * cap + 32) * width

def scaleTime (overhead : Nat → Nat) (width termCap accumulatorCap mulTime : Nat) : Nat :=
  let fee := overhead (128 * scaleWidth width (accumulatorCap + termCap))
  termCap * (mulTime + 65 * fee) + 64 * fee

/-- The scaling fold reserves room for every remaining term. The original input
and accumulator stay in the retained context and contribute to every fee. -/
theorem scalePrepend_time {indexTy : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (ts acc : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (coeff : F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width termCap accumulatorCap mulTime : Nat)
    (hh : header ≤ width) (he : Q.size (rep.env Γ) env ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : ∀ t ∈ ts, Q.size (rep.ty (termTy indexTy)) t ≤ width)
    (ha : ∀ t ∈ acc, Q.size (rep.ty (termTy indexTy)) t ≤ 3 * width)
    (htc : ts.length ≤ termCap) (hac : acc.length ≤ accumulatorCap)
    (hm : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (scalePrepend (Γ := Γ))).time (ts, coeff, acc, env) ≤
        scaleTime overhead width termCap accumulatorCap mulTime := by
  let cap := accumulatorCap + termCap
  let W := scaleWidth width cap
  let fee := overhead (128 * W)
  let step := fun (t : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (saved : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) => (t.1, coeff * t.2) :: saved
  let inv := fun remaining (saved : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) =>
    saved.length + remaining ≤ cap ∧ ∀ t ∈ saved, Q.size (rep.ty (termTy indexTy)) t ≤ 3 * width
  have hw : width ≤ W := by dsimp [W, scaleWidth]; nlinarith
  have hprod := @sizes.prod_le
  have hcoeff := hf coeff
  have hscaled (t : indexTy.Value (cryptoBase F G₁ G₂ K M) × F) (hit : t ∈ ts) :
      Q.size (rep.ty (termTy indexTy)) (t.1, coeff * t.2) ≤ 3 * width := by
    have hindex := (sizes.fst_le (rep.ty indexTy) (rep.ty scalar) t).trans (ht t hit)
    have hscalar := hf (coeff * t.2)
    have hp := sizes.prod_le (rep.ty indexTy) (rep.ty scalar) (t.1, coeff * t.2)
    dsimp only at hp
    exact hp.trans (by omega)
  have hlist (ys : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F))
      (hlen : ys.length ≤ cap) (hy : ∀ y ∈ ys, Q.size (rep.ty (termTy indexTy)) y ≤ 3 * width) :
      Q.size (rep.ty (.list (termTy indexTy))) ys ≤ (4 * cap + 1) * width := by
    have h := lists.size_le_cap (rep.ty (termTy indexTy)) ys (3 * width) cap hy hlen
    change Q.size (rep.ty (.list (termTy indexTy))) ys ≤ _ at h
    nlinarith [Nat.mul_le_mul_left cap hh]
  have hts := hlist ts (htc.trans (by omega)) (fun t hit => (ht t hit).trans (by omega))
  have hacc := hlist acc (hac.trans (by omega)) ha
  have hretained : Q.size (rep.env ([.list (termTy indexTy), scalar, .list (termTy indexTy)] ++ Γ))
      (ts, coeff, acc, env) ≤ (8 * cap + 8) * width := by
    dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty,
      List.cons_append, List.nil_append, List.append] at *
    grind only
  have hfold (ys saved : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F))
      (hy : ∀ y ∈ ys, y ∈ ts) (hs : inv ys.length saved) :
      inv 0 (ys.foldl (fun saved t => step t saved) saved) := by
    induction ys generalizing saved with
    | nil => exact hs
    | cons y ys ih =>
        apply ih (step y saved) (fun z hz => hy z (by simp [hz]))
        refine ⟨by dsimp only [step]; simp only [List.length_cons] at *; have := hs.1; omega, ?_⟩
        intro t hit
        rcases List.mem_cons.mp hit with rfl | hit
        · exact hscaled y (hy y (by simp))
        · exact hs.2 t hit
  have hwork := foldWork_bound_remaining step
    (fun t saved => (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost)
      primitive laws dataLaws primitiveBound
      (scaleBody (indexTy := indexTy) (Γ := .list (termTy indexTy) :: Γ))).time
        (t, saved, ts, coeff, acc, env))
    (foldFee (Q := Q) overhead rep.data (rep.ty (termTy indexTy))
      (rep.ty (.list (termTy indexTy)))
      (rep.env ([.list (termTy indexTy), scalar, .list (termTy indexTy)] ++ Γ))
      (fun p => (p.1.1, p.2.2.2.1 * p.1.2) :: p.2.1) (ts, coeff, acc, env))
    (fun t => t ∈ ts) inv (mulTime + 64 * fee) fee cap
    (by
      intro remaining hr t hit saved hs
      have hsSize := hlist saved (by have := hs.1; omega) hs.2
      have htSize := ht t hit
      have hroot : Q.size (rep.env (termTy indexTy :: .list (termTy indexTy) ::
          .list (termTy indexTy) :: scalar :: .list (termTy indexTy) :: Γ))
          (t, saved, ts, coeff, acc, env) ≤ W := by
        dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty] at *
        dsimp only [W, scaleWidth]
        grind only
      have hbody := scaleBody_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        (indexTy := indexTy) (Γ := .list (termTy indexTy) :: Γ)
        (t, saved, ts, coeff, acc, env) W mulTime (hh.trans hw) hroot
        (fun f => (hf f).trans hw) hm
      refine ⟨hbody, ?_⟩
      refine ⟨by dsimp only [step]; simp only [List.length_cons]; have := hs.1; omega, ?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hscaled t hit
      · exact hs.2 u hu)
    (by
      intro ys hlen hy saved hs
      have hysSize := hlist ys hlen (fun y hit => (ht y (hy y hit)).trans (by omega))
      have hsSize := hlist saved (by have := hs.1; omega) hs.2
      have ho := hfold ys saved hy hs
      have hoSize := hlist (ys.foldl (fun saved t => step t saved) saved) (by have := ho.1; omega) ho.2
      unfold foldFee
      apply mono
      dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env, step, W, scaleWidth,
        List.cons_append, List.nil_append, List.append] at *
      grind only)
    ts (htc.trans (by omega)) (fun _ h => h) acc ⟨by omega, ha⟩
  have ho := hfold ts acc (fun _ h => h) ⟨by omega, ha⟩
  have hout := hlist (ts.foldl (fun saved t => step t saved) acc) (by have := ho.1; omega) ho.2
  have hfee : ∀ n ≤ 128 * W, overhead n ≤ fee := fun _ hn => mono hn
  have hcap := Nat.mul_le_mul_right (mulTime + 65 * fee) htc
  have hmulValue : ∀ x y : F, (arithmetic F G₁ G₂ K M cost).execute .mul (x, y) = x * y :=
    fun _ _ => rfl
  clear ho hfold hlist hscaled inv ht ha hf hm
  dsimp only [scalePrepend, scaleBody, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.foldBound, Expr.denote, Var.get, LanguageRepresentation.ty,
    LanguageRepresentation.env, step, scaleTime, scaleWidth, fee, W, cap,
    List.cons_append, List.nil_append, List.append, id] at *
  simp only [hmulValue] at *
  grind only

include laws dataLaws in
theorem scalePrepend_cost {indexTy : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (ts acc : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (coeff : F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width termCap accumulatorCap mulTime : Nat)
    (hh : header ≤ width) (he : Q.size (rep.env Γ) env ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : ∀ t ∈ ts, Q.size (rep.ty (termTy indexTy)) t ≤ width)
    (ha : ∀ t ∈ acc, Q.size (rep.ty (termTy indexTy)) t ≤ 3 * width)
    (htc : ts.length ≤ termCap) (hac : acc.length ≤ accumulatorCap)
    (hm : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (scalePrepend (Γ := Γ))) (ts, coeff, acc, env) ≤
        scaleTime overhead width termCap accumulatorCap mulTime :=
  (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound (scalePrepend (Γ := Γ)) (ts, coeff, acc, env)).trans
      (scalePrepend_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        ts acc coeff env width termCap accumulatorCap mulTime hh he hf ht ha htc hac hm)

end Signatures.Runtime.WeightedAGM.Coefficients
