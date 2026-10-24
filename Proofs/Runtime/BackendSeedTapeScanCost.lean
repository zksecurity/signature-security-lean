import Proofs.Runtime.BackendReverseCost
import Proofs.Runtime.SeedTapeCellBounds
import Proofs.Runtime.Weakening

/-! Native retained-tape scan costs. The expressions below are definitionally
the existing scan weakened by an arbitrary retained context. The cost bounds
charge that context, the original list, the accumulator and the final reversal. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.SeedTape.NativeScan

open BackendProgram

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private abbrev v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))

def body {Γ : List (Ty CryptoAtom)} :
    Expr CryptoOp (Replay.Mixed.event :: popState :: .nat :: .list Replay.Mixed.event :: Γ) popState :=
  let keep := Expr.pair (.fst v1) (.pair (.fst (.snd v1)) (.cons v0 (.snd (.snd v1))))
  .branch (.fst v1) keep
    (.branch (.op .natEq (.pair (.fst v0) v2))
      (.pair (.bool true) (.pair v0 (.snd (.snd v1)))) keep)

theorem body_eq (Γ : List (Ty CryptoAtom)) : popBody.weakenTail Γ = body (Γ := Γ) := rfl

def forward {Γ : List (Ty CryptoAtom)} :
    Expr CryptoOp (.nat :: .list Replay.Mixed.event :: Γ) popState :=
  .fold v1 (.pair (.bool false) (.pair Replay.Mixed.emptyEvent .nil)) body

theorem forward_eq (Γ : List (Ty CryptoAtom)) : popFold.weakenTail Γ = forward (Γ := Γ) := rfl

def scanWith {Γ : List (Ty CryptoAtom)}
    (first : Expr CryptoOp (.nat :: .list Replay.Mixed.event :: Γ) popState)
    (reverse : Expr CryptoOp (.list Replay.Mixed.event :: popState :: .nat :: .list Replay.Mixed.event :: Γ)
      (.list Replay.Mixed.event)) : Expr CryptoOp (.nat :: .list Replay.Mixed.event :: Γ) popState :=
  .letE first (.pair (.fst v0) (.pair (.fst (.snd v0))
    (.letE (.snd (.snd v0)) reverse)))

def scan {Γ : List (Ty CryptoAtom)} : Expr CryptoOp (.nat :: .list Replay.Mixed.event :: Γ) popState :=
  scanWith forward reverseList

theorem scan_eq (Γ : List (Ty CryptoAtom)) : popCode.weakenTail Γ = scan (Γ := Γ) := rfl

def Invariant {F : Type} (valid : TapeCell F → Prop) (cap remaining : Nat)
    (acc : Bool × TapeCell F × List (TapeCell F)) : Prop :=
  acc.2.2.length + remaining ≤ cap ∧ valid acc.2.1 ∧ ∀ x ∈ acc.2.2, valid x

theorem step_invariant {F : Type} (valid : TapeCell F → Prop) (tag cap remaining : Nat)
    (x : TapeCell F) (acc : Bool × TapeCell F × List (TapeCell F))
    (hx : valid x) (ha : Invariant valid cap (remaining + 1) acc) :
    Invariant valid cap remaining (popStep tag acc x) := by
  obtain ⟨found, answer, rest⟩ := acc
  obtain ⟨hl, hv, hr⟩ := ha
  cases found <;> by_cases same : x.1 = tag <;>
    simp only [popStep, Bool.false_eq_true, same, ↓reduceIte] <;>
    refine ⟨?_, by assumption, ?_⟩
  all_goals first
    | (simp only [List.length_cons] at *; omega)
    | (intro y hy; rcases List.mem_cons.mp hy with rfl | hy
       · exact hx
       · exact hr y hy)

theorem fold_invariant {F : Type} (valid : TapeCell F → Prop) (tag cap : Nat)
    (xs : List (TapeCell F)) (acc : Bool × TapeCell F × List (TapeCell F))
    (hx : ∀ x ∈ xs, valid x) (ha : Invariant valid cap xs.length acc) :
    Invariant valid cap 0 (xs.foldl (popStep tag) acc) := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons x xs ih =>
      apply ih (popStep tag acc x) (fun y hy => hx y (by simp [hy]))
      exact step_invariant valid tag cap xs.length x acc (hx x (by simp)) ha

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem body_denote {Γ : List (Ty CryptoAtom)} (cost : PrimitiveCosts)
    (x : TapeCell F) (acc : Bool × TapeCell F × List (TapeCell F))
    (tag : Nat) (xs : List (TapeCell F)) (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    body.denote (arithmetic F G₁ G₂ K M cost) (x, acc, tag, xs, env) = popStep tag acc x := by
  rw [← body_eq]
  exact (Expr.weakenTail_denote (Δ := Γ) (arithmetic F G₁ G₂ K M cost)
    popBody (x, acc, tag, xs, ()) env).trans (popBody_denote cost x acc tag xs)

theorem forward_denote {Γ : List (Ty CryptoAtom)} (cost : PrimitiveCosts)
    (tag : Nat) (xs : List (TapeCell F)) (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    forward.denote (arithmetic F G₁ G₂ K M cost) (tag, xs, env) =
      xs.foldl (popStep tag) (false, (0, (0 : F), 0), []) := by
  rw [← forward_eq]
  exact (Expr.weakenTail_denote (Δ := Γ) (arithmetic F G₁ G₂ K M cost)
    popFold (tag, xs, ()) env).trans (popFold_denote cost tag xs)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
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

theorem body_time {Γ : List (Ty CryptoAtom)}
    (x : TapeCell F) (acc : Bool × TapeCell F × List (TapeCell F))
    (tag : Nat) (xs : List (TapeCell F)) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width comparisonTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hi : Q.size (rep.env (Replay.Mixed.event :: popState :: .nat :: .list Replay.Mixed.event :: Γ))
      (x, acc, tag, xs, env) ≤ width)
    (heq : (primitiveBound .natEq).time (x.1, tag) ≤ comparisonTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (body (Γ := Γ))).time (x, acc, tag, xs, env) ≤ comparisonTime + 512 * overhead (256 * width) := by
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hsum := @sizes.sum_le
  have hcons := @lists.cons_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  obtain ⟨found, answer, rest⟩ := acc
  cases found <;> by_cases same : x.1 = tag <;>
    dsimp only [body, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity, LocalBound.elim,
    LocalBound.castFunction, DataCostLaws.selectBound, DataCostLaws.boolBound, DataCostLaws.unitBound,
    DataCostLaws.consBound, Expr.denote, Var.get, arithmetic,
    LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def, Sum.elim] at * <;>
    simp only [same, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] at * <;>
    grind only

omit [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [C.HasSum] [C.HasOption] [Q.HasCategory] QP QS sizes mono in
theorem list_size (width cap : Nat) (hh : header ≤ width) (xs : List (TapeCell F))
    (hx : ∀ x ∈ xs, Q.size (rep.ty Replay.Mixed.event) x ≤ width) (hc : xs.length ≤ cap) :
    Q.size (rep.ty (.list Replay.Mixed.event)) xs ≤ (2 * cap + 1) * width := by
  have h := lists.size_le_cap (rep.ty Replay.Mixed.event) xs width cap hx hc
  change Q.size (rep.ty (.list Replay.Mixed.event)) xs ≤ _ at h
  nlinarith [Nat.mul_le_mul_left cap hh]

omit [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [Q.HasCategory] QP QS mono in
theorem accumulator_size (width cap remaining : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (acc : Bool × TapeCell F × List (TapeCell F))
    (ha : Invariant (fun x => Q.size (rep.ty Replay.Mixed.event) x ≤ width) cap remaining acc) :
    Q.size (rep.ty popState) acc ≤ (2 * cap + 5) * width := by
  obtain ⟨hl, hv, hr⟩ := ha
  have hs := list_size rep lists width cap hh acc.2.2 hr (by omega)
  have hp := @sizes.prod_le
  dsimp only [LanguageRepresentation.ty] at *
  grind only

def frameWidth (width cap : Nat) : Nat := (8 * cap + 32) * width

def forwardTime (overhead : Nat → Nat) (width cap comparisonTime zeroTime : Nat) : Nat :=
  cap * (comparisonTime + 513 * overhead (256 * frameWidth width cap)) +
    zeroTime + 64 * overhead (256 * frameWidth width cap)

theorem forward_time {Γ : List (Ty CryptoAtom)}
    (tag : Nat) (xs : List (TapeCell F)) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width cap comparisonTime zeroTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : Q.size rep.data.nat tag ≤ width) (he : Q.size (rep.env Γ) env ≤ width)
    (hd : Q.size (rep.ty Replay.Mixed.event) (0, (0 : F), 0) ≤ width)
    (hx : ∀ x ∈ xs, Q.size (rep.ty Replay.Mixed.event) x ≤ width) (hc : xs.length ≤ cap)
    (hcompare : ∀ x ∈ xs, (primitiveBound .natEq).time (x.1, tag) ≤ comparisonTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (forward (Γ := Γ))).time (tag, xs, env) ≤ forwardTime overhead width cap comparisonTime zeroTime := by
  let W := frameWidth width cap
  let fee := overhead (256 * W)
  let valid := fun x : TapeCell F => Q.size (rep.ty Replay.Mixed.event) x ≤ width
  let inv := Invariant valid cap
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hxs := list_size rep lists width cap hh xs hx hc
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcontext : Q.size (rep.env (.nat :: .list Replay.Mixed.event :: Γ)) (tag, xs, env) ≤
      (2 * cap + 5) * width := by
    dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty] at *
    grind only
  have bodyFunction : (body (Γ := Γ)).denote (arithmetic F G₁ G₂ K M cost) =
      fun p => popStep p.2.2.1 p.2.1 p.1 := by
    funext p
    exact body_denote cost p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
  have hwork := foldWork_bound_remaining (fun x acc => popStep tag acc x)
    (fun x acc => (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound (body (Γ := Γ))).time (x, acc, tag, xs, env))
    (foldFee (Q := Q) overhead rep.data (rep.ty Replay.Mixed.event) (rep.ty popState)
      (rep.env (.nat :: .list Replay.Mixed.event :: Γ))
      (fun p => popStep p.2.2.1 p.2.1 p.1) (tag, xs, env))
    (fun x => x ∈ xs) inv (comparisonTime + 512 * fee) fee cap
    (by
      intro remaining hremaining x member acc ha
      have haSize := accumulator_size rep sizes lists width cap (remaining + 1) hh hb acc ha
      have hxSize := hx x member
      have hroot : Q.size (rep.env (Replay.Mixed.event :: popState :: .nat :: .list Replay.Mixed.event :: Γ))
          (x, acc, tag, xs, env) ≤ W := by
        dsimp only [LanguageRepresentation.env, W, frameWidth] at *
        grind only
      exact ⟨body_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
          x acc tag xs env W comparisonTime (hh.trans hw) (hu.trans hw)
          (fun b => (hb b).trans hw) hroot (hcompare x member),
        step_invariant valid tag cap remaining x acc hxSize ha⟩)
    (by
      intro ys hlen hys acc ha
      have hysSize := list_size rep lists width cap hh ys (fun x member => hx x (hys x member)) hlen
      have haSize := accumulator_size rep sizes lists width cap ys.length hh hb acc ha
      have ho := fold_invariant valid tag cap ys acc (fun x member => hx x (hys x member)) ha
      have hoSize := accumulator_size rep sizes lists width cap 0 hh hb _ ho
      unfold foldFee
      apply mono
      dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env, fee, W, frameWidth] at *
      grind only)
    xs hc (fun _ member => member) (false, (0, (0 : F), 0), []) ⟨by simpa, hd, by simp⟩
  have houtInv := fold_invariant valid tag cap xs (false, (0, (0 : F), 0), []) hx
    ⟨by simpa, hd, by simp⟩
  have hout := accumulator_size rep sizes lists width cap 0 hh hb _ houtInv
  have hnil := lists.nil_le (rep.ty Replay.Mixed.event)
  have hfee : ∀ n ≤ 256 * W, overhead n ≤ fee := fun _ hn => mono hn
  have hcap := Nat.mul_le_mul_right (comparisonTime + 513 * fee) hc
  dsimp only [forward, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.foldBound, DataCostLaws.unitBound, DataCostLaws.boolBound,
    DataCostLaws.natBound, DataCostLaws.nilBound, Expr.denote, Var.get,
    Replay.Mixed.emptyEvent, arithmetic, LanguageRepresentation.ty, LanguageRepresentation.env,
    id, Function.comp_def, forwardTime, fee, W, frameWidth, foldFee] at *
  simp only [bodyFunction]
  grind only

omit lists in
private theorem scanWith_time {Γ : List (Ty CryptoAtom)}
    (first : Expr CryptoOp (.nat :: .list Replay.Mixed.event :: Γ) popState)
    (reverse : Expr CryptoOp (.list Replay.Mixed.event :: popState :: .nat :: .list Replay.Mixed.event :: Γ)
      (.list Replay.Mixed.event))
    (tag : Nat) (xs : List (TapeCell F)) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width firstTime reverseTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env (.nat :: .list Replay.Mixed.event :: Γ)) (tag, xs, env) ≤ width)
    (hf : Q.size (rep.ty popState) (first.denote (arithmetic F G₁ G₂ K M cost) (tag, xs, env)) ≤ width)
    (hr : Q.size (rep.ty (.list Replay.Mixed.event))
      (reverse.denote (arithmetic F G₁ G₂ K M cost)
        ((first.denote (arithmetic F G₁ G₂ K M cost) (tag, xs, env)).2.2,
          first.denote (arithmetic F G₁ G₂ K M cost) (tag, xs, env), tag, xs, env)) ≤ width)
    (ht : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound first).time (tag, xs, env) ≤ firstTime)
    (hu : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound reverse).time
        ((first.denote (arithmetic F G₁ G₂ K M cost) (tag, xs, env)).2.2,
          first.denote (arithmetic F G₁ G₂ K M cost) (tag, xs, env), tag, xs, env) ≤ reverseTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (scanWith first reverse)).time (tag, xs, env) ≤
        firstTime + reverseTime + 256 * overhead (256 * width) := by
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  dsimp only [scanWith, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    Expr.denote, Var.get, LanguageRepresentation.ty, LanguageRepresentation.env,
    id, Function.comp_def] at *
  grind only

def scanTime (overhead : Nat → Nat) (width cap comparisonTime zeroTime : Nat) : Nat :=
  let W := frameWidth width cap
  forwardTime overhead width cap comparisonTime zeroTime +
    cap * (17 * overhead (128 * ((4 * cap + 8) * W))) +
      16 * overhead (128 * ((4 * cap + 8) * W)) + 256 * overhead (256 * W)

/-- The original scan in any retained context, including the reverse that
restores chronological order. Runtime depends on tape length and encoded width. -/
theorem scan_time {Γ : List (Ty CryptoAtom)}
    (tag : Nat) (xs : List (TapeCell F)) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width cap comparisonTime zeroTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : Q.size rep.data.nat tag ≤ width) (he : Q.size (rep.env Γ) env ≤ width)
    (hd : Q.size (rep.ty Replay.Mixed.event) (0, (0 : F), 0) ≤ width)
    (hx : ∀ x ∈ xs, Q.size (rep.ty Replay.Mixed.event) x ≤ width) (hc : xs.length ≤ cap)
    (hcompare : ∀ x ∈ xs, (primitiveBound .natEq).time (x.1, tag) ≤ comparisonTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (popCode.weakenTail Γ)).time (tag, xs, env) ≤ scanTime overhead width cap comparisonTime zeroTime := by
  let W := frameWidth width cap
  let acc := xs.foldl (popStep tag) (false, (0, (0 : F), 0), [])
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have ha := fold_invariant (fun x => Q.size (rep.ty Replay.Mixed.event) x ≤ width)
    tag cap xs (false, (0, (0 : F), 0), []) hx ⟨by simpa, hd, by simp⟩
  have hacc := accumulator_size rep sizes lists width cap 0 hh hb acc ha
  have hxs := list_size rep lists width cap hh xs hx hc
  have hrest : acc.2.2.length ≤ cap := by have := ha.1; omega
  have hrev := list_size rep lists width cap hh acc.2.2.reverse
    (fun x member => ha.2.2 x (List.mem_reverse.mp member)) (by simpa using hrest)
  have hp := @sizes.prod_le
  have hin : Q.size (rep.env (.nat :: .list Replay.Mixed.event :: Γ)) (tag, xs, env) ≤ W := by
    dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, W, frameWidth] at *
    grind only
  have hcontext : Q.size (rep.env (popState :: .nat :: .list Replay.Mixed.event :: Γ))
      (acc, tag, xs, env) ≤ W := by
    dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, W, frameWidth] at *
    grind only
  have hfirst := forward_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    tag xs env width cap comparisonTime zeroTime hh hu hb hn he hd hx hc hcompare hzero
  have hreverse := ReverseCompiler.reverse_time_bound
    (cell := Replay.Mixed.event) (Γ := popState :: .nat :: .list Replay.Mixed.event :: Γ)
    rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes lists mono
    acc.2.2 (acc, tag, xs, env) W cap (hh.trans hw) (hu.trans hw) hcontext
    (fun x member => (ha.2.2 x member).trans hw) hrest
  have h := scanWith_time rep data cost primitive laws dataLaws primitiveBound sizes mono
    forward reverseList tag xs env W (forwardTime overhead width cap comparisonTime zeroTime)
    (cap * (17 * overhead (128 * ((4 * cap + 8) * W))) + 16 * overhead (128 * ((4 * cap + 8) * W)))
    (hh.trans hw) hin
    (by rw [forward_denote]; exact hacc.trans (by dsimp [W, frameWidth]; nlinarith))
    (by rw [reverseList_denote, forward_denote]; exact hrev.trans (by dsimp [W, frameWidth]; nlinarith))
    hfirst (by rw [forward_denote]; exact hreverse)
  rw [scan_eq]
  exact h.trans (by dsimp only [scanTime, W]; omega)

include laws dataLaws in
theorem scan_cost {Γ : List (Ty CryptoAtom)}
    (tag : Nat) (xs : List (TapeCell F)) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width cap comparisonTime zeroTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : Q.size rep.data.nat tag ≤ width) (he : Q.size (rep.env Γ) env ≤ width)
    (hd : Q.size (rep.ty Replay.Mixed.event) (0, (0 : F), 0) ≤ width)
    (hx : ∀ x ∈ xs, Q.size (rep.ty Replay.Mixed.event) x ≤ width) (hc : xs.length ≤ cap)
    (hcompare : ∀ x ∈ xs, (primitiveBound .natEq).time (x.1, tag) ≤ comparisonTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (popCode.weakenTail Γ)) (tag, xs, env) ≤ scanTime overhead width cap comparisonTime zeroTime :=
  (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
    _ _).trans (scan_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      tag xs env width cap comparisonTime zeroTime hh hu hb hn he hd hx hc hcompare hzero)

end Signatures.Runtime.Schnorr.SeedTape.NativeScan
