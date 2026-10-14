import Signatures.Runtime.BackendWeightedExpandStep
import Signatures.Runtime.BackendReverseCost

/-! Native accounting for the complete outer coefficient-row fold and final
reversal. The invariant reserves the output of every remaining signing reply.
The generic generator premise is discharged by the scheme generator theorems. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Coefficients

open Terms BackendProgram

private def rowsWith {indexTy messageTy : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (body : Expr CryptoOp (rowTy messageTy :: .list (termTy indexTy) :: .list (rowTy messageTy) :: Γ)
      (.list (termTy indexTy)))
    (reverse : Expr CryptoOp (.list (termTy indexTy) :: .list (rowTy messageTy) :: Γ)
      (.list (termTy indexTy))) :
    Expr CryptoOp (.list (rowTy messageTy) :: Γ) (.list (termTy indexTy)) :=
  .letE (.fold (.var .here) .nil body) reverse

def expandRowsWidth (width rowCap termCap : Nat) : Nat :=
  (8 * (rowCap * termCap) + 8 * rowCap + 32) * width

def expandRowsTime (overhead : Nat → Nat) (width rowCap termCap termTime mulTime : Nat) : Nat :=
  let W := expandRowsWidth width rowCap termCap
  let cap := rowCap * termCap
  let fee := overhead (128 * W)
  let reverseFee := overhead (128 * ((4 * cap + 8) * W))
  rowCap * (expandStepTime overhead W termCap cap termTime mulTime + fee) +
    cap * (17 * reverseFee) + 16 * reverseFee + 65 * fee

universe v w

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

private theorem rowsWith_time {indexTy messageTy : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (body : Expr CryptoOp (rowTy messageTy :: .list (termTy indexTy) :: .list (rowTy messageTy) :: Γ)
      (.list (termTy indexTy)))
    (reverse : Expr CryptoOp (.list (termTy indexTy) :: .list (rowTy messageTy) :: Γ)
      (.list (termTy indexTy)))
    (rows : List ((messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁) × F))
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width foldTime reverseTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env (.list (rowTy messageTy) :: Γ)) (rows, env) ≤ width)
    (ho : Q.size (rep.ty (.list (termTy indexTy)))
      (rows.foldl (fun acc row => body.denote (arithmetic F G₁ G₂ K M cost) (row, acc, rows, env)) []) ≤ width)
    (hr : Q.size (rep.ty (.list (termTy indexTy)))
      (reverse.denote (arithmetic F G₁ G₂ K M cost)
        (rows.foldl (fun acc row => body.denote (arithmetic F G₁ G₂ K M cost) (row, acc, rows, env)) [],
          rows, env)) ≤ width)
    (hw : foldWork
      (fun row acc => body.denote (arithmetic F G₁ G₂ K M cost) (row, acc, rows, env))
      (fun row acc => (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws
        dataLaws primitiveBound body).time (row, acc, rows, env))
      (foldFee (Q := Q) overhead rep.data (rep.ty (rowTy messageTy)) (rep.ty (.list (termTy indexTy)))
        (rep.env (.list (rowTy messageTy) :: Γ)) (body.denote (arithmetic F G₁ G₂ K M cost)) (rows, env))
      rows [] ≤ foldTime)
    (ht : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound reverse).time
        (rows.foldl (fun acc row => body.denote (arithmetic F G₁ G₂ K M cost) (row, acc, rows, env)) [],
          rows, env) ≤ reverseTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (rowsWith body reverse)).time (rows, env) ≤
        foldTime + reverseTime + 64 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hnil := lists.nil_le (rep.ty (termTy indexTy))
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [rowsWith, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.identity, DataCostLaws.foldBound,
    DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env, id] at *
  grind only

/-- Full row expansion and reversal, with one generator bound at the largest
retained frame. Scheme instantiations derive that bound from primitive costs. -/
theorem expandRows_time {indexTy messageTy : Ty CryptoAtom}
    (terms : Expr CryptoOp [messageTy] (.list (termTy indexTy)))
    (rows : List ((messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁) × F))
    {Γ : List (Ty CryptoAtom)} (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width rowCap termCap termTime mulTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width)
    (hr : ∀ row ∈ rows, Q.size (rep.ty (rowTy messageTy)) row ≤ width)
    (hc : rows.length ≤ rowCap)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : ∀ row ∈ rows, ∀ t ∈ terms.denote (arithmetic F G₁ G₂ K M cost) (row.1.1, ()),
      Q.size (rep.ty (termTy indexTy)) t ≤ width)
    (hlen : ∀ row ∈ rows,
      (terms.denote (arithmetic F G₁ G₂ K M cost) (row.1.1, ())).length ≤ termCap)
    (hgen : ∀ row ∈ rows, ∀ (Δ : List (Ty CryptoAtom)) (tail : Env (cryptoBase F G₁ G₂ K M) Δ),
      Q.size (rep.env Δ) tail ≤ expandRowsWidth width rowCap termCap →
      (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
        primitiveBound (terms.weakenTail Δ)).time (row.1.1, tail) ≤ termTime)
    (hm : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (expandRows terms)).time (rows, env) ≤
        expandRowsTime overhead width rowCap termCap termTime mulTime := by
  let cap := rowCap * termCap
  let W := expandRowsWidth width rowCap termCap
  let fee := overhead (128 * W)
  let bodyTime := expandStepTime overhead W termCap cap termTime mulTime
  let step := fun row acc => (expandStep terms (Γ := .list (rowTy messageTy) :: Γ)).denote
    (arithmetic F G₁ G₂ K M cost) (row, acc, rows, env)
  let inv := fun remaining (acc : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) =>
    acc.length + remaining * termCap ≤ cap ∧ ∀ t ∈ acc, Q.size (rep.ty (termTy indexTy)) t ≤ 3 * width
  have hw3 : 3 * width ≤ W := by
    dsimp only [W, expandRowsWidth]
    exact Nat.mul_le_mul_right width (by omega)
  have hw : width ≤ W := by omega
  have hprod := @sizes.prod_le
  have hrowList (ys : List ((messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁) × F))
      (hy : ∀ y ∈ ys, y ∈ rows) (hl : ys.length ≤ rowCap) :
      Q.size (rep.ty (.list (rowTy messageTy))) ys ≤ (2 * rowCap + 1) * width := by
    have h := lists.size_le_cap (rep.ty (rowTy messageTy)) ys width rowCap (fun y hit => hr y (hy y hit)) hl
    change Q.size (rep.ty (.list (rowTy messageTy))) ys ≤ _ at h
    nlinarith [Nat.mul_le_mul_left rowCap hh]
  have hlist (ys : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F))
      (hl : ys.length ≤ cap) (hy : ∀ y ∈ ys, Q.size (rep.ty (termTy indexTy)) y ≤ 3 * width) :
      Q.size (rep.ty (.list (termTy indexTy))) ys ≤ (4 * cap + 1) * width := by
    have h := lists.size_le_cap (rep.ty (termTy indexTy)) ys (3 * width) cap hy hl
    change Q.size (rep.ty (.list (termTy indexTy))) ys ≤ _ at h
    nlinarith [Nat.mul_le_mul_left cap hh]
  have hrows := hrowList rows (fun _ h => h) hc
  have henv : Q.size (rep.env (.list (rowTy messageTy) :: Γ)) (rows, env) ≤ W := by
    dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, W, expandRowsWidth] at *
    grind only
  have hstep remaining row (hit : row ∈ rows) acc (ha : inv (remaining + 1) acc) :
      inv remaining (step row acc) := by
    dsimp only [step]
    rw [expandStep_denote]
    refine ⟨?_, ?_⟩
    · simp only [List.length_append, List.length_reverse, List.length_map]
      have hcount := hlen row hit
      have hcap := ha.1
      nlinarith
    · intro t ht'
      rcases List.mem_append.mp ht' with ht' | ht'
      · obtain ⟨u, hu', rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ht')
        have hi := (sizes.fst_le (rep.ty indexTy) (rep.ty scalar) u).trans (ht row hit u hu')
        have hs := hf (row.2 * u.2)
        have hp := sizes.prod_le (rep.ty indexTy) (rep.ty scalar) (u.1, row.2 * u.2)
        dsimp only at hp
        exact hp.trans (by omega)
      · exact ha.2 t ht'
  have hfold (ys : List ((messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁) × F))
      (hy : ∀ y ∈ ys, y ∈ rows) (acc : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F))
      (ha : inv ys.length acc) : inv 0 (ys.foldl (fun acc row => step row acc) acc) := by
    induction ys generalizing acc with
    | nil => exact ha
    | cons y ys ih =>
        exact ih (fun z hz => hy z (by simp [hz])) (step y acc)
          (hstep ys.length y (hy y (by simp)) acc ha)
  have hinit : inv rows.length [] := by
    refine ⟨?_, by simp⟩
    simpa only [List.length_nil, Nat.zero_add] using Nat.mul_le_mul_right termCap hc
  have hwork := foldWork_bound_remaining step
    (fun row acc => (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (expandStep terms (Γ := .list (rowTy messageTy) :: Γ))).time (row, acc, rows, env))
    (foldFee (Q := Q) overhead rep.data (rep.ty (rowTy messageTy)) (rep.ty (.list (termTy indexTy)))
      (rep.env (.list (rowTy messageTy) :: Γ))
      ((expandStep terms (Γ := .list (rowTy messageTy) :: Γ)).denote (arithmetic F G₁ G₂ K M cost)) (rows, env))
    (fun row => row ∈ rows) inv bodyTime fee rowCap
    (by
      intro remaining _ row hit acc ha
      have hac : acc.length ≤ cap := by have := ha.1; omega
      have haSize := hlist acc hac ha.2
      have hrSize := hr row hit
      have hframe : Q.size (rep.env
          (rowTy messageTy :: .list (termTy indexTy) :: .list (rowTy messageTy) :: Γ))
          (row, acc, rows, env) ≤ W := by
        dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, W, expandRowsWidth, cap] at *
        grind only
      refine ⟨?_, hstep remaining row hit acc ha⟩
      exact expandStep_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        terms row acc (Γ := .list (rowTy messageTy) :: Γ) (rows, env) W termCap cap termTime mulTime
        (hh.trans hw) henv (hrSize.trans hw) (fun f => (hf f).trans hw)
        (fun t ht' => (ht row hit t ht').trans hw)
        (fun t ht' => (ha.2 t ht').trans (Nat.mul_le_mul_left 3 hw)) (hlen row hit) hac
        (hgen row hit (rowTy messageTy :: .list (termTy indexTy) :: .list (rowTy messageTy) :: Γ)
          (row, acc, rows, env) hframe) hm)
    (by
      intro ys hlength hy acc ha
      have hysSize := hrowList ys hy hlength
      have haSize := hlist acc (by have := ha.1; omega) ha.2
      have ho := hfold ys hy acc ha
      have hoSize := hlist (ys.foldl (fun acc row => step row acc) acc) (by have := ho.1; omega) ho.2
      unfold foldFee
      apply mono
      dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env, step, W, expandRowsWidth, cap] at *
      grind only)
    rows hc (fun _ h => h) [] hinit
  have hout := hfold rows (fun _ h => h) [] hinit
  have houtCap : (rows.foldl (fun acc row => step row acc) []).length ≤ cap := by
    simpa only [Nat.zero_mul, Nat.add_zero] using hout.1
  have houtSize := hlist _ houtCap hout.2
  have houtputWidth : (4 * cap + 1) * width ≤ W := by
    dsimp only [W, expandRowsWidth, cap]
    exact Nat.mul_le_mul_right width (by omega)
  have houtW : Q.size (rep.ty (.list (termTy indexTy)))
      (rows.foldl (fun acc row => step row acc) []) ≤ W :=
    houtSize.trans houtputWidth
  have hreverseSize := hlist (rows.foldl (fun acc row => step row acc) []).reverse
    (by simpa only [List.length_reverse] using houtCap)
    (fun t hit => hout.2 t (List.mem_reverse.mp hit))
  have hreverse := ReverseCompiler.reverse_time_bound rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound sizes lists mono (rows.foldl (fun acc row => step row acc) [])
    (Γ := .list (rowTy messageTy) :: Γ) (rows, env) W cap (hh.trans hw) (hu.trans hw) henv
    (fun t hit => (hout.2 t hit).trans hw3) houtCap
  have hworkCap := hwork.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (bodyTime + fee) hc) fee)
  have htime := rowsWith_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (expandStep terms (Γ := .list (rowTy messageTy) :: Γ)) reverseList rows env W
    (rowCap * (bodyTime + fee) + fee)
    (cap * (17 * overhead (128 * ((4 * cap + 8) * W))) + 16 * overhead (128 * ((4 * cap + 8) * W)))
    (hh.trans hw) (hu.trans hw) henv houtW
    (by rw [reverseList_denote]; exact hreverseSize.trans houtputWidth)
    hworkCap hreverse
  change (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound (expandRows terms)).time (rows, env) ≤ _ at htime
  dsimp only [expandRowsTime, bodyTime, fee, W, cap] at htime ⊢
  omega

end Signatures.Runtime.WeightedAGM.Coefficients
