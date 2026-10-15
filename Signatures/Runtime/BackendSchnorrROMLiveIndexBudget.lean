import Signatures.Runtime.BackendSchnorrROMLiveIndexFold

/-! Complete native chronological lookup, including reversal and all retained
environments. The primitive bounds concern encountered cells, not a message domain. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeSelection

open BackendProgram

private def indexWith {Γ}
    (reverse : Expr CryptoOp ([hashCache, hashKey, hashCache] ++ Γ) hashCache)
    (scan : Expr CryptoOp ([hashKey, hashCache, hashKey, hashCache] ++ Γ) indexResult) :
    Expr CryptoOp ([hashKey, hashCache] ++ Γ) indexResult :=
  .letE (.letE (.var (.there .here)) reverse)
    (.letE (.var (.there .here)) scan)

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

include sizes mono

private theorem indexWith_time {Γ}
    (reverse : Expr CryptoOp ([hashCache, hashKey, hashCache] ++ Γ) hashCache)
    (scan : Expr CryptoOp ([hashKey, hashCache, hashKey, hashCache] ++ Γ) indexResult)
    (key : M × G₁) (xs : List ((M × G₁) × F)) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width reverseTime scanTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env ([hashKey, hashCache] ++ Γ)) (key, xs, env) ≤ width)
    (hr : Q.size (rep.ty hashCache)
      (reverse.denote (arithmetic F G₁ G₂ K M cost) (xs, key, xs, env)) ≤ width)
    (ho : Q.size (rep.ty indexResult)
      (scan.denote (arithmetic F G₁ G₂ K M cost)
        (key, reverse.denote (arithmetic F G₁ G₂ K M cost) (xs, key, xs, env), key, xs, env)) ≤ width)
    (hreverse : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      reverse).time (xs, key, xs, env) ≤ reverseTime)
    (hscan : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      scan).time (key, reverse.denote (arithmetic F G₁ G₂ K M cost) (xs, key, xs, env), key, xs, env) ≤ scanTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (indexWith reverse scan)).time (key, xs, env) ≤ reverseTime + scanTime + 64 * overhead (64 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 64 * width, overhead n ≤ overhead (64 * width) := fun _ hn => mono hn
  dsimp only [indexWith, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    Expr.denote, Var.get, id, Function.comp_def] at *
  simp only [List.cons_append, List.nil_append, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  dsimp only [List.append, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  grind only

def indexWidth (width cap : Nat) : Nat := (4 * cap + 16) * width

def indexTime (overhead : Nat → Nat) (width cap messageTime pointTime incrementTime : Nat) : Nat :=
  let W := indexWidth width cap
  cap * (17 * overhead (128 * ((4 * cap + 8) * W))) +
    16 * overhead (128 * ((4 * cap + 8) * W)) +
    indexFoldTime overhead W cap messageTime pointTime incrementTime + 64 * overhead (64 * W)

include lists

theorem liveIndex_time {Γ : List (Ty CryptoAtom)}
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
      (liveIndex.weakenTail Γ)).time (key, xs, env) ≤
      indexTime overhead width cap messageTime pointTime incrementTime := by
  let W := indexWidth width cap
  have hw : width ≤ W := by dsimp [W, indexWidth]; nlinarith
  have hprod := @sizes.prod_le
  have hlist (ys : List ((M × G₁) × F)) (hl : ys.length ≤ cap) (hy : ∀ y ∈ ys, y ∈ xs) :
      Q.size (rep.ty hashCache) ys ≤ (2 * cap + 1) * width := by
    have h := lists.size_le_cap (rep.ty (.pair hashKey scalar)) ys width cap (fun y hy' => hx y (hy y hy')) hl
    change Q.size (rep.ty hashCache) ys ≤ _ at h
    nlinarith [Nat.mul_le_mul_left cap hh]
  have hxs := hlist xs hlen (fun _ h => h)
  have hrlen : xs.reverse.length ≤ cap := by simpa using hlen
  have hrmem : ∀ x ∈ xs.reverse, x ∈ xs := by simp
  have hreverseSize := hlist xs.reverse hrlen hrmem
  have henv : Q.size (rep.env ([hashKey, hashCache] ++ Γ)) (key, xs, env) ≤ W := by
    simp only [List.cons_append, List.nil_append, LanguageRepresentation.env] at *
    dsimp only [W, indexWidth]
    grind only
  have hr := ReverseCompiler.reverse_time_bound rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound sizes lists mono (cell := .pair hashKey scalar) (Γ := [hashKey, hashCache] ++ Γ)
    xs (key, xs, env) W cap (hh.trans hw) (hu.trans hw) henv
    (fun x hx' => (hx x hx').trans hw) hlen
  have hs := liveIndexFold_time rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    (Γ := [hashKey, hashCache] ++ Γ) key xs.reverse (key, xs, env) W cap messageTime pointTime incrementTime
    (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) (fun n hn' => (hn n hn').trans hw)
    (hk.trans hw) henv (fun x hx' => (hx x (hrmem x hx')).trans hw) hrlen
    (fun x hx' => hm x (hrmem x hx')) (fun x hx' => hp x (hrmem x hx')) hadd
  have hscanValue := liveIndexFold.weakenTail_denote (Δ := [hashKey, hashCache] ++ Γ)
    (arithmetic F G₁ G₂ K M cost) (key, xs.reverse, ()) (key, xs, env)
  simp only [Env.append] at hscanValue
  rw [liveIndexFold_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)] at hscanValue
  have ho : Q.size (rep.ty indexResult)
      ((liveIndexFold.weakenTail ([hashKey, hashCache] ++ Γ)).denote (arithmetic F G₁ G₂ K M cost)
        (key, xs.reverse, key, xs, env)) ≤ W := by
    rw [hscanValue]
    have hn' := hn (xs.reverse.findIdx (fun x => decide (x.1 = key)))
      (by have h := List.findIdx_le_length (xs := xs.reverse) (p := fun x => decide (x.1 = key)); omega)
    have hb' := hb (xs.reverse.any (fun x => decide (x.1 = key)))
    have hp' := sizes.prod_le rep.data.bool rep.data.nat
      (xs.reverse.any (fun x => decide (x.1 = key)), xs.reverse.findIdx (fun x => decide (x.1 = key)))
    change Q.size (rep.ty indexResult) _ ≤ _ at hp'
    dsimp only [W, indexWidth]
    nlinarith only [hp', hb', hn', hh]
  have ht := indexWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    (reverseList (cell := .pair hashKey scalar) (Γ := [hashKey, hashCache] ++ Γ))
    (liveIndexFold.weakenTail ([hashKey, hashCache] ++ Γ)) key xs env W
    (cap * (17 * overhead (128 * ((4 * cap + 8) * W))) + 16 * overhead (128 * ((4 * cap + 8) * W)))
    (indexFoldTime overhead W cap messageTime pointTime incrementTime) (hh.trans hw) henv
    (by rw [reverseList_denote]; dsimp only [W, indexWidth]; nlinarith)
    (by rw [reverseList_denote]; exact ho) hr (by rw [reverseList_denote]; exact hs)
  exact ht

include laws dataLaws in
theorem liveIndex_cost {Γ : List (Ty CryptoAtom)}
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
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (liveIndex.weakenTail Γ)) (key, xs, env) ≤
      indexTime overhead width cap messageTime pointTime incrementTime :=
  (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound _ _).trans
      (liveIndex_time rep data cost primitive sizes lists laws dataLaws primitiveBound mono
        key xs env width cap messageTime pointTime incrementTime hh hu hb hn hk he hx hlen hm hp hadd)

end Signatures.Runtime.Schnorr.ListROM.NativeSelection
