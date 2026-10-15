import Signatures.Runtime.SchnorrAGMFlatten

/-! Derive the native affine-sum fold's cost from field instructions and encoded
frame sizes. The accumulator has two field elements throughout the traversal. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Flatten

open BackendProgram

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

include sizes mono

theorem body_time {Γ : List (Ty CryptoAtom)}
    (input : Env (cryptoBase F G₁ G₂ K M) (rowTy :: affineTy :: Γ))
    (width mulTime addTime : Nat) (hh : header ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hi : Q.size (rep.env (rowTy :: affineTy :: Γ)) input ≤ width)
    (hm : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (ha : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ addTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound body).time input ≤ 2 * mulTime + 2 * addTime + 256 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hm₁ := hm input.1.2 input.1.1.1
  have hm₂ := hm input.1.2 input.1.1.2
  have ha₁ := ha input.2.1.1 (input.1.2 * input.1.1.1)
  have ha₂ := ha input.2.1.2 (input.1.2 * input.1.1.2)
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [body, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    Expr.denote, Var.get, arithmetic, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  clear hm ha
  grind only

def sumWidth (width cap : Nat) : Nat := (6 * cap + 32) * width

def sumTime (overhead : Nat → Nat) (width cap mulTime addTime : Nat) : Nat :=
  let fee := overhead (128 * sumWidth width cap)
  cap * (2 * mulTime + 2 * addTime + 257 * fee) + 32 * fee

include lists in
theorem sumRows_time {Γ : List (Ty CryptoAtom)} (rows : List ((F × F) × F)) (z : F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width cap mulTime addTime : Nat)
    (hh : header ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hc : rows.length ≤ cap)
    (hm : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (ha : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ addTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound sumRows).time (rows, z, env) ≤ sumTime overhead width cap mulTime addTime := by
  let W := sumWidth width cap
  let fee := overhead (128 * W)
  let step := fun (row : (F × F) × F) (acc : F × F) =>
    (body (Γ := rowsTy :: scalar :: Γ)).denote (arithmetic F G₁ G₂ K M cost) (row, acc, rows, z, env)
  have hw : width ≤ W := by dsimp [W, sumWidth]; nlinarith
  have hp (p : F × F) : Q.size (rep.ty affineTy) p ≤ 3 * width := by
    have h := sizes.prod_le (rep.ty scalar) (rep.ty scalar) p
    have h₁ := hf p.1
    have h₂ := hf p.2
    exact h.trans (by omega)
  have hr (row : (F × F) × F) : Q.size (rep.ty rowTy) row ≤ 5 * width := by
    have h := sizes.prod_le (rep.ty affineTy) (rep.ty scalar) row
    have h₁ := hp row.1
    have h₂ := hf row.2
    exact h.trans (by omega)
  have hl (xs : List ((F × F) × F)) (hn : xs.length ≤ cap) :
      Q.size (rep.ty rowsTy) xs ≤ (6 * cap + 1) * width := by
    have h := lists.size_le_cap (rep.ty rowTy) xs (5 * width) cap (fun r _ => hr r) hn
    change Q.size (rep.ty rowsTy) xs ≤ _ at h
    nlinarith [Nat.mul_le_mul_left cap hh]
  have hrows := hl rows hc
  have hz := hf z
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have henv : Q.size (rep.env (rowsTy :: scalar :: Γ)) (rows, z, env) ≤ W := by
    dsimp only [W, sumWidth, LanguageRepresentation.env] at *
    grind only
  have hwork := foldWork_bound step
    (fun row acc => (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (body (Γ := rowsTy :: scalar :: Γ))).time (row, acc, rows, z, env))
    (foldFee (Q := Q) overhead rep.data (rep.ty rowTy) (rep.ty affineTy) (rep.env (rowsTy :: scalar :: Γ))
      ((body (Γ := rowsTy :: scalar :: Γ)).denote (arithmetic F G₁ G₂ K M cost)) (rows, z, env))
    (fun _ => True) (fun _ => True) (2 * mulTime + 2 * addTime + 256 * fee) fee cap
    (by
      intro row _ acc _
      have hrow := hr row
      have hacc := hp acc
      have hroot : Q.size (rep.env (rowTy :: affineTy :: rowsTy :: scalar :: Γ))
          (row, acc, rows, z, env) ≤ W := by
        dsimp only [W, sumWidth, LanguageRepresentation.env] at *
        grind only
      exact ⟨body_time (Γ := rowsTy :: scalar :: Γ) rep data cost primitive laws dataLaws primitiveBound sizes mono
        (row, acc, rows, z, env) W mulTime addTime (hh.trans hw) (fun f => (hf f).trans hw) hroot hm ha,
        True.intro⟩)
    (by
      intro xs hlen _ acc _
      have hxs := hl xs hlen
      have hacc := hp acc
      have hout := hp (xs.foldl (fun acc row => step row acc) acc)
      unfold foldFee
      apply mono
      dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env, step, W, sumWidth] at *
      clear hm ha
      grind only)
    rows hc (fun _ _ => True.intro) (z, z) True.intro
  have hinit := hp (z, z)
  have hout := hp (rows.foldl (fun acc row => step row acc) (z, z))
  have hfee : ∀ n ≤ 128 * W, overhead n ≤ fee := fun _ hn => mono hn
  have hcap := Nat.mul_le_mul_right (2 * mulTime + 2 * addTime + 257 * fee) hc
  dsimp only [sumRows, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.foldBound, Expr.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env, step, id, sumTime, fee, W] at *
  clear hm ha
  grind only

end Signatures.Runtime.SchnorrAGM.Native.Flatten
