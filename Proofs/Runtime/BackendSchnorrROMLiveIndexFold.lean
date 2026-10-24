import Proofs.Runtime.BackendSchnorrROMLiveIndexCost

/-! Complete native index-fold cost with a remaining-cell counter invariant.
The original cache and trailing environment are retained and charged throughout. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeSelection

open BackendProgram

theorem findStep_count {A B : Type} [DecidableEq A] (key : A) (acc : Bool × Nat) (cell : A × B) :
    (findStep key acc cell).2 ≤ acc.2 + 1 := by
  unfold findStep
  split
  · omega
  · split <;> simp only <;> omega

theorem findStep_fold_count {A B : Type} [DecidableEq A] (key : A) (xs : List (A × B)) (acc : Bool × Nat) :
    (xs.foldl (findStep key) acc).2 ≤ acc.2 + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      have h := ih (findStep key acc x)
      have hs := findStep_count key acc x
      simp only [List.foldl_cons, List.length_cons]
      omega

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
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

def indexFoldWidth (width cap : Nat) : Nat := (16 * cap + 64) * width

def indexFoldTime (overhead : Nat → Nat) (width cap messageTime pointTime incrementTime : Nat) : Nat :=
  let fee := overhead (256 * indexFoldWidth width cap)
  cap * (messageTime + pointTime + incrementTime + 1025 * fee) + 64 * fee

include sizes lists mono

theorem liveIndexFold_time {Γ : List (Ty CryptoAtom)}
    (key : M × G₁) (xs : List ((M × G₁) × F)) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width cap messageTime pointTime incrementTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ cap + 1, Q.size rep.data.nat n ≤ width)
    (hk : Q.size (rep.ty hashKey) key ≤ width) (he : Q.size (rep.env Γ) env ≤ width)
    (hx : ∀ x ∈ xs, Q.size (rep.ty (.pair hashKey scalar)) x ≤ width) (hlen : xs.length ≤ cap)
    (hm : ∀ x ∈ xs, (primitiveBound .messageEq).time (x.1.1, key.1) ≤ messageTime)
    (hp : ∀ x ∈ xs, (primitiveBound .point₁Eq).time (x.1.2, key.2) ≤ pointTime)
    (hadd : ∀ n ≤ cap, (primitiveBound .natAdd).time (n, 1) ≤ incrementTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (liveIndexFold.weakenTail Γ)).time (key, xs, env) ≤
      indexFoldTime overhead width cap messageTime pointTime incrementTime := by
  let W := indexFoldWidth width cap
  let fee := overhead (256 * W)
  let inv := fun remaining (acc : Bool × Nat) => acc.2 + remaining ≤ cap
  let step := fun (x : (M × G₁) × F) (acc : Bool × Nat) => findStep key acc x
  have hw : width ≤ W := by dsimp [W, indexFoldWidth]; nlinarith
  have hprod := @sizes.prod_le
  have hlist (ys : List ((M × G₁) × F)) (hl : ys.length ≤ cap) (hy : ∀ y ∈ ys, y ∈ xs) :
      Q.size (rep.ty hashCache) ys ≤ (2 * cap + 1) * width := by
    have h := lists.size_le_cap (rep.ty (.pair hashKey scalar)) ys width cap (fun y hy' => hx y (hy y hy')) hl
    change Q.size (rep.ty hashCache) ys ≤ _ at h
    nlinarith [Nat.mul_le_mul_left cap hh]
  have hacc (acc : Bool × Nat) (ha : acc.2 ≤ cap) : Q.size (rep.ty indexResult) acc ≤ 3 * width := by
    have h := sizes.prod_le rep.data.bool rep.data.nat acc
    have hbool := hb acc.1
    have hnat := hn acc.2 (by omega)
    change Q.size (rep.ty indexResult) acc ≤ _ at h
    omega
  have hxs := hlist xs hlen (fun _ h => h)
  have henv : Q.size (rep.env ([hashKey, hashCache] ++ Γ)) (key, xs, env) ≤ (2 * cap + 5) * width := by
    simp only [List.cons_append, List.nil_append, LanguageRepresentation.env] at *
    grind only
  have bodyFunction : (liveIndexBody.weakenTail Γ).denote (arithmetic F G₁ G₂ K M cost) =
      fun p => findStep p.2.2.1 p.2.1 p.1 := by
    funext p
    obtain ⟨cell, acc, target, original, tail⟩ := p
    have h := liveIndexBody.weakenTail_denote (Δ := Γ) (arithmetic F G₁ G₂ K M cost)
      (cell, acc, target, original, ()) tail
    simpa only [Env.append] using h.trans
      (liveIndexBody_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost cell acc target original)
  have hwork := foldWork_bound_remaining step
    (fun x acc => (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (liveIndexBody.weakenTail Γ)).time (x, acc, key, xs, env))
    (foldFee (Q := Q) overhead rep.data (rep.ty (.pair hashKey scalar)) (rep.ty indexResult)
      (rep.env ([hashKey, hashCache] ++ Γ)) (fun p => findStep p.2.2.1 p.2.1 p.1) (key, xs, env))
    (fun x => x ∈ xs) inv (messageTime + pointTime + incrementTime + 1024 * fee) fee cap
    (by
      intro remaining _ x member acc ha
      have haccCount : acc.2 ≤ cap := by dsimp only [inv] at ha; omega
      have haSize := hacc acc haccCount
      have hxSize := hx x member
      have hroot : Q.size (rep.env ([.pair hashKey scalar, indexResult, hashKey, hashCache] ++ Γ))
          (x, acc, key, xs, env) ≤ W := by
        simp only [List.cons_append, List.nil_append, LanguageRepresentation.env] at *
        dsimp only [W, indexFoldWidth]
        grind only
      have ht := liveIndexBody_time rep data cost primitive sizes laws dataLaws primitiveBound mono
        x acc key xs env W messageTime pointTime incrementTime (hh.trans hw) (hu.trans hw)
        (fun b => (hb b).trans hw) ((hn 1 (by omega)).trans hw)
        ((hn (acc.2 + 1) (by omega)).trans hw) hroot (hm x member) (hp x member) (hadd acc.2 haccCount)
      refine ⟨ht, ?_⟩
      have hstep := findStep_count key acc x
      dsimp only [inv, step] at *
      omega)
    (by
      intro ys hl hy acc ha
      have hys := hlist ys hl hy
      have haSize := hacc acc (by dsimp only [inv] at ha; omega)
      have hc := findStep_fold_count key ys acc
      have hoSize := hacc (ys.foldl (findStep key) acc) (by dsimp only [inv] at ha; omega)
      unfold foldFee
      apply mono
      simp only [List.cons_append, List.nil_append, LanguageRepresentation.ty, LanguageRepresentation.env] at *
      dsimp only [fee, W, indexFoldWidth, step] at *
      grind only)
    xs hlen (fun _ h => h) (false, 0) (by simpa [inv])
  have hfinalCount := findStep_fold_count key xs (false, 0)
  have hout := hacc (xs.foldl (findStep key) (false, 0)) (by simp only at hfinalCount; omega)
  have hzero := hn 0 (by omega)
  have hbool := hb false
  have hfee : ∀ n ≤ 256 * W, overhead n ≤ fee := fun _ hn' => mono hn'
  have hcap := Nat.mul_le_mul_right (messageTime + pointTime + incrementTime + 1025 * fee) hlen
  dsimp only [liveIndexFold, Expr.weakenTail, Var.weakenTail, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.foldBound, DataCostLaws.unitBound, DataCostLaws.boolBound, DataCostLaws.natBound,
    Expr.denote, Var.get, arithmetic, id, Function.comp_def, indexFoldTime] at *
  simp only [bodyFunction, List.cons_append, List.nil_append, LanguageRepresentation.ty, LanguageRepresentation.env] at *
  dsimp only [step, fee, W, indexFoldWidth] at *
  dsimp only [List.append, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  clear hm hp hadd hx hn hacc hlist
  grind only

end Signatures.Runtime.Schnorr.ListROM.NativeSelection
