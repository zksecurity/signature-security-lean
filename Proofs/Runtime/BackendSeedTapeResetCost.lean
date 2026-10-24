import Proofs.Runtime.BackendSeedTapeScanCost

/-! Native costs for trimming one retained-tape family and installing its
replacement. Iteration follows the stored list, never the numeric reset slot. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.SeedTape.NativeReset

open BackendProgram

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private abbrev v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
private abbrev v4 {a b c d e Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: Γ) e :=
  .var (.there (.there (.there (.there .here))))

def body {Γ : List (Ty CryptoAtom)} :
    Expr CryptoOp (Replay.Mixed.event :: trimState :: .nat :: .nat :: .list Replay.Mixed.event :: Γ) trimState :=
  .branch (.op .natEq (.pair (.fst v0) v2))
    (.branch (.op .natEq (.pair (.fst v1) (.nat 0))) v1
      (.pair (.op .natSub (.pair (.fst v1) (.nat 1))) (.cons v0 (.snd v1))))
    (.pair (.fst v1) (.cons v0 (.snd v1)))

theorem body_eq (Γ : List (Ty CryptoAtom)) : trimBody (Γ := Γ) = body (Γ := Γ) := rfl

def forward {Γ : List (Ty CryptoAtom)} :
    Expr CryptoOp (.nat :: .nat :: .list Replay.Mixed.event :: Γ) trimState :=
  .fold v2 (.pair v1 .nil) body

theorem forward_eq (Γ : List (Ty CryptoAtom)) : trimFold (Γ := Γ) = forward (Γ := Γ) := rfl

def resetWith {Γ : List (Ty CryptoAtom)}
    (first : Expr CryptoOp (.nat :: .nat :: .list Replay.Mixed.event :: Replay.Mixed.event :: Γ) trimState)
    (reverse : Expr CryptoOp
      (.list Replay.Mixed.event :: trimState :: .nat :: .nat :: .list Replay.Mixed.event :: Replay.Mixed.event :: Γ)
      (.list Replay.Mixed.event)) :
    Expr CryptoOp (.nat :: .nat :: .list Replay.Mixed.event :: Replay.Mixed.event :: Γ) (.list Replay.Mixed.event) :=
  .letE first (.letE (.cons v4 (.snd v0)) reverse)

def expression {Γ : List (Ty CryptoAtom)} :
    Expr CryptoOp (.nat :: .nat :: .list Replay.Mixed.event :: Replay.Mixed.event :: Γ) (.list Replay.Mixed.event) :=
  resetWith forward reverseList

theorem expression_eq (Γ : List (Ty CryptoAtom)) : resetCode.weakenTail Γ = expression (Γ := Γ) := rfl

def Invariant {F : Type} (valid : TapeCell F → Prop) (cap counterCap remaining : Nat)
    (acc : Nat × List (TapeCell F)) : Prop :=
  acc.1 ≤ counterCap ∧ acc.2.length + remaining ≤ cap ∧ ∀ x ∈ acc.2, valid x

theorem step_invariant {F : Type} (valid : TapeCell F → Prop) (tag cap counterCap remaining : Nat)
    (x : TapeCell F) (acc : Nat × List (TapeCell F))
    (hx : valid x) (ha : Invariant valid cap counterCap (remaining + 1) acc) :
    Invariant valid cap counterCap remaining (trimStep tag acc x) := by
  obtain ⟨counter, rest⟩ := acc
  obtain ⟨hn, hl, hv⟩ := ha
  dsimp only at hn hl hv
  by_cases same : x.1 = tag <;> by_cases zero : counter = 0 <;>
    simp only [trimStep, same, zero, ↓reduceIte] <;>
    refine ⟨by omega, by simp only [List.length_cons]; omega, ?_⟩
  all_goals first
    | exact hv
    | (intro y hy; rcases List.mem_cons.mp hy with rfl | hy
       · exact hx
       · exact hv y hy)

theorem fold_invariant {F : Type} (valid : TapeCell F → Prop) (tag cap counterCap : Nat)
    (xs : List (TapeCell F)) (acc : Nat × List (TapeCell F))
    (hx : ∀ x ∈ xs, valid x) (ha : Invariant valid cap counterCap xs.length acc) :
    Invariant valid cap counterCap 0 (xs.foldl (trimStep tag) acc) := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons x xs ih =>
      apply ih (trimStep tag acc x) (fun y hy => hx y (by simp [hy]))
      exact step_invariant valid tag cap counterCap xs.length x acc (hx x (by simp)) ha

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem body_denote {Γ : List (Ty CryptoAtom)} (cost : PrimitiveCosts)
    (x : TapeCell F) (acc : Nat × List (TapeCell F)) (tag slot : Nat)
    (xs : List (TapeCell F)) (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    body.denote (arithmetic F G₁ G₂ K M cost) (x, acc, tag, slot, xs, env) = trimStep tag acc x :=
  trimBody_denote cost env x acc tag slot xs

theorem forward_denote {Γ : List (Ty CryptoAtom)} (cost : PrimitiveCosts) (tag slot : Nat)
    (xs : List (TapeCell F)) (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    forward.denote (arithmetic F G₁ G₂ K M cost) (tag, slot, xs, env) =
      xs.foldl (trimStep tag) (slot, []) := by
  change xs.foldl (fun acc x => body.denote (arithmetic F G₁ G₂ K M cost)
    (x, acc, tag, slot, xs, env)) (slot, []) = _
  simp_rw [body_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]

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

theorem body_time {Γ : List (Ty CryptoAtom)} (x : TapeCell F) (acc : Nat × List (TapeCell F))
    (tag slot : Nat) (xs : List (TapeCell F)) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width comparisonTime subtractTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hsubSize : Q.size rep.data.nat (acc.1 - 1) ≤ width)
    (hi : Q.size (rep.env (Replay.Mixed.event :: trimState :: .nat :: .nat :: .list Replay.Mixed.event :: Γ))
      (x, acc, tag, slot, xs, env) ≤ width)
    (heq : (primitiveBound .natEq).time (x.1, tag) ≤ comparisonTime)
    (hzero : (primitiveBound .natEq).time (acc.1, 0) ≤ comparisonTime)
    (hsub : (primitiveBound .natSub).time (acc.1, 1) ≤ subtractTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (body (Γ := Γ))).time (x, acc, tag, slot, xs, env) ≤
        2 * comparisonTime + subtractTime + 512 * overhead (256 * width) := by
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hsum := @sizes.sum_le
  have hcons := @lists.cons_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  by_cases same : x.1 = tag <;> by_cases zero : acc.1 = 0 <;>
    dsimp only [body, Expression.compileBound, Expression.variableBound, LocalBound.compose,
      LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity, LocalBound.elim,
      LocalBound.castFunction, DataCostLaws.selectBound, DataCostLaws.natBound, DataCostLaws.unitBound,
      DataCostLaws.consBound, Expr.denote, Var.get, arithmetic,
      LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def, Sum.elim] at * <;>
    simp only [same, zero, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] at * <;>
    grind only

omit [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [Q.HasCategory] QP QS mono in
theorem accumulator_size (width cap counterCap remaining : Nat) (hh : header ≤ width)
    (hn : ∀ n ≤ counterCap, Q.size rep.data.nat n ≤ width) (acc : Nat × List (TapeCell F))
    (ha : Invariant (fun x => Q.size (rep.ty Replay.Mixed.event) x ≤ width) cap counterCap remaining acc) :
    Q.size (rep.ty trimState) acc ≤ (2 * cap + 3) * width := by
  have hs := NativeScan.list_size rep lists width cap hh acc.2 ha.2.2 (by have := ha.2.1; omega)
  have hc := hn acc.1 ha.1
  have hp := sizes.prod_le rep.data.nat (rep.ty (.list Replay.Mixed.event)) acc
  change Q.size (rep.ty trimState) acc ≤ _ at hp
  nlinarith

def frameWidth (width cap : Nat) : Nat := (8 * cap + 32) * width

def forwardTime (overhead : Nat → Nat) (width cap comparisonTime subtractTime : Nat) : Nat :=
  cap * (2 * comparisonTime + subtractTime + 513 * overhead (256 * frameWidth width cap)) +
    64 * overhead (256 * frameWidth width cap)

theorem forward_time {Γ : List (Ty CryptoAtom)} (tag slot : Nat) (xs : List (TapeCell F))
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width cap counterCap comparisonTime subtractTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hn : ∀ n ≤ counterCap, Q.size rep.data.nat n ≤ width) (hslot : slot ≤ counterCap)
    (htag : Q.size rep.data.nat tag ≤ width) (he : Q.size (rep.env Γ) env ≤ width)
    (hx : ∀ x ∈ xs, Q.size (rep.ty Replay.Mixed.event) x ≤ width) (hc : xs.length ≤ cap)
    (hcompare : ∀ x ∈ xs, (primitiveBound .natEq).time (x.1, tag) ≤ comparisonTime)
    (hzero : ∀ n ≤ counterCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
    (hsub : ∀ n ≤ counterCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (forward (Γ := Γ))).time (tag, slot, xs, env) ≤ forwardTime overhead width cap comparisonTime subtractTime := by
  let W := frameWidth width cap
  let fee := overhead (256 * W)
  let valid := fun x : TapeCell F => Q.size (rep.ty Replay.Mixed.event) x ≤ width
  let inv := Invariant valid cap counterCap
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hxs := NativeScan.list_size rep lists width cap hh xs hx hc
  have hslotSize := hn slot hslot
  have hp := @sizes.prod_le
  have hcontext : Q.size (rep.env (.nat :: .nat :: .list Replay.Mixed.event :: Γ)) (tag, slot, xs, env) ≤
      (2 * cap + 7) * width := by
    dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty] at *
    grind only
  have bodyFunction : (body (Γ := Γ)).denote (arithmetic F G₁ G₂ K M cost) =
      fun p => trimStep p.2.2.1 p.2.1 p.1 := by
    funext p
    exact body_denote cost p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2
  have hwork := foldWork_bound_remaining (fun x acc => trimStep tag acc x)
    (fun x acc => (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound (body (Γ := Γ))).time (x, acc, tag, slot, xs, env))
    (foldFee (Q := Q) overhead rep.data (rep.ty Replay.Mixed.event) (rep.ty trimState)
      (rep.env (.nat :: .nat :: .list Replay.Mixed.event :: Γ))
      (fun p => trimStep p.2.2.1 p.2.1 p.1) (tag, slot, xs, env))
    (fun x => x ∈ xs) inv (2 * comparisonTime + subtractTime + 512 * fee) fee cap
    (by
      intro remaining hremaining x member acc ha
      have haSize := accumulator_size rep sizes lists width cap counterCap (remaining + 1) hh hn acc ha
      have hxSize := hx x member
      have hroot : Q.size (rep.env (Replay.Mixed.event :: trimState :: .nat :: .nat :: .list Replay.Mixed.event :: Γ))
          (x, acc, tag, slot, xs, env) ≤ W := by
        dsimp only [LanguageRepresentation.env, W, frameWidth] at *
        grind only
      exact ⟨body_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
          x acc tag slot xs env W comparisonTime subtractTime (hh.trans hw) (hu.trans hw)
          (fun b => (hb b).trans hw) (hn0.trans hw) (hn1.trans hw)
          ((hn (acc.1 - 1) ((Nat.sub_le _ _).trans ha.1)).trans hw) hroot
          (hcompare x member) (hzero acc.1 ha.1) (hsub acc.1 ha.1),
        step_invariant valid tag cap counterCap remaining x acc hxSize ha⟩)
    (by
      intro ys hlen hys acc ha
      have hysSize := NativeScan.list_size rep lists width cap hh ys (fun x member => hx x (hys x member)) hlen
      have haSize := accumulator_size rep sizes lists width cap counterCap ys.length hh hn acc ha
      have ho := fold_invariant valid tag cap counterCap ys acc (fun x member => hx x (hys x member)) ha
      have hoSize := accumulator_size rep sizes lists width cap counterCap 0 hh hn _ ho
      unfold foldFee
      apply mono
      dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env, fee, W, frameWidth] at *
      grind only)
    xs hc (fun _ member => member) (slot, []) ⟨hslot, by simpa, by simp⟩
  have houtInv := fold_invariant valid tag cap counterCap xs (slot, []) hx ⟨hslot, by simpa, by simp⟩
  have hout := accumulator_size rep sizes lists width cap counterCap 0 hh hn _ houtInv
  have hnil := lists.nil_le (rep.ty Replay.Mixed.event)
  have hfee : ∀ n ≤ 256 * W, overhead n ≤ fee := fun _ hn => mono hn
  have hcap := Nat.mul_le_mul_right (2 * comparisonTime + subtractTime + 513 * fee) hc
  dsimp only [forward, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.foldBound, DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def, forwardTime, fee, W, frameWidth] at *
  simp only [bodyFunction]
  grind only

private theorem resetWith_time {Γ : List (Ty CryptoAtom)}
    (first : Expr CryptoOp (.nat :: .nat :: .list Replay.Mixed.event :: Replay.Mixed.event :: Γ) trimState)
    (reverse : Expr CryptoOp
      (.list Replay.Mixed.event :: trimState :: .nat :: .nat :: .list Replay.Mixed.event :: Replay.Mixed.event :: Γ)
      (.list Replay.Mixed.event))
    (tag slot : Nat) (xs : List (TapeCell F)) (answer : TapeCell F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width firstTime reverseTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env (.nat :: .nat :: .list Replay.Mixed.event :: Replay.Mixed.event :: Γ))
      (tag, slot, xs, answer, env) ≤ width)
    (hf : Q.size (rep.ty trimState)
      (first.denote (arithmetic F G₁ G₂ K M cost) (tag, slot, xs, answer, env)) ≤ width)
    (hr : Q.size (rep.ty (.list Replay.Mixed.event))
      (reverse.denote (arithmetic F G₁ G₂ K M cost)
        (answer :: (first.denote (arithmetic F G₁ G₂ K M cost) (tag, slot, xs, answer, env)).2,
          first.denote (arithmetic F G₁ G₂ K M cost) (tag, slot, xs, answer, env), tag, slot, xs, answer, env)) ≤ width)
    (ht : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound first).time (tag, slot, xs, answer, env) ≤ firstTime)
    (hu : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound reverse).time
        (answer :: (first.denote (arithmetic F G₁ G₂ K M cost) (tag, slot, xs, answer, env)).2,
          first.denote (arithmetic F G₁ G₂ K M cost) (tag, slot, xs, answer, env), tag, slot, xs, answer, env) ≤ reverseTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (resetWith first reverse)).time (tag, slot, xs, answer, env) ≤
        firstTime + reverseTime + 256 * overhead (256 * width) := by
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcons := @lists.cons_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  dsimp only [resetWith, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.consBound, Expr.denote, Var.get, LanguageRepresentation.ty, LanguageRepresentation.env,
    id, Function.comp_def] at *
  grind only

def resetTime (overhead : Nat → Nat) (width cap comparisonTime subtractTime : Nat) : Nat :=
  let W := frameWidth width cap
  forwardTime overhead width cap comparisonTime subtractTime +
    (cap + 1) * (17 * overhead (128 * ((4 * (cap + 1) + 8) * W))) +
      16 * overhead (128 * ((4 * (cap + 1) + 8) * W)) + 256 * overhead (256 * W)

/-- Runtime for the existing reset expression with any retained context.
The counter's numeric cap bounds primitive inputs, not the iteration count. -/
theorem reset_time {Γ : List (Ty CryptoAtom)} (tag slot : Nat) (xs : List (TapeCell F))
    (answer : TapeCell F) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width cap counterCap comparisonTime subtractTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hn : ∀ n ≤ counterCap, Q.size rep.data.nat n ≤ width) (hslot : slot ≤ counterCap)
    (htag : Q.size rep.data.nat tag ≤ width)
    (he : Q.size (rep.env (Replay.Mixed.event :: Γ)) (answer, env) ≤ width)
    (hx : ∀ x ∈ xs, Q.size (rep.ty Replay.Mixed.event) x ≤ width) (hc : xs.length ≤ cap)
    (hcompare : ∀ x ∈ xs, (primitiveBound .natEq).time (x.1, tag) ≤ comparisonTime)
    (hzero : ∀ n ≤ counterCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
    (hsub : ∀ n ≤ counterCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (resetCode.weakenTail Γ)).time (tag, slot, xs, answer, env) ≤
        resetTime overhead width cap comparisonTime subtractTime := by
  let W := frameWidth width cap
  let acc := xs.foldl (trimStep tag) (slot, [])
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hslotSize := hn slot hslot
  have hanswer : Q.size (rep.ty Replay.Mixed.event) answer ≤ width :=
    (sizes.fst_le (rep.ty Replay.Mixed.event) (rep.env Γ) (answer, env)).trans he
  have ha := fold_invariant (fun x => Q.size (rep.ty Replay.Mixed.event) x ≤ width)
    tag cap counterCap xs (slot, []) hx ⟨hslot, by simpa, by simp⟩
  have hacc := accumulator_size rep sizes lists width cap counterCap 0 hh hn acc ha
  have hxs := NativeScan.list_size rep lists width cap hh xs hx hc
  have hrest : acc.2.length ≤ cap := by have := ha.2.1; omega
  have hnew : ∀ x ∈ answer :: acc.2, Q.size (rep.ty Replay.Mixed.event) x ≤ width := by
    intro x member
    rcases List.mem_cons.mp member with rfl | member
    · exact hanswer
    · exact ha.2.2 x member
  have hrev := NativeScan.list_size rep lists width (cap + 1) hh (answer :: acc.2).reverse
    (fun x member => hnew x (List.mem_reverse.mp member)) (by simpa using Nat.add_le_add_right hrest 1)
  have hp := @sizes.prod_le
  have hin : Q.size (rep.env (.nat :: .nat :: .list Replay.Mixed.event :: Replay.Mixed.event :: Γ))
      (tag, slot, xs, answer, env) ≤ W := by
    dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, W, frameWidth] at *
    grind only
  have hcontext : Q.size (rep.env (trimState :: .nat :: .nat :: .list Replay.Mixed.event :: Replay.Mixed.event :: Γ))
      (acc, tag, slot, xs, answer, env) ≤ W := by
    dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, W, frameWidth] at *
    grind only
  have hfirst := forward_time (Γ := Replay.Mixed.event :: Γ)
    rep data cost primitive laws dataLaws primitiveBound sizes lists mono tag slot xs (answer, env)
    width cap counterCap comparisonTime subtractTime hh hu hb hn0 hn1 hn hslot htag he hx hc hcompare hzero hsub
  have hreverse := ReverseCompiler.reverse_time_bound
    (cell := Replay.Mixed.event) (Γ := trimState :: .nat :: .nat :: .list Replay.Mixed.event :: Replay.Mixed.event :: Γ)
    rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes lists mono
    (answer :: acc.2) (acc, tag, slot, xs, answer, env) W (cap + 1) (hh.trans hw) (hu.trans hw) hcontext
    (fun x member => (hnew x member).trans hw) (by simpa using Nat.add_le_add_right hrest 1)
  have h := resetWith_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    forward reverseList tag slot xs answer env W (forwardTime overhead width cap comparisonTime subtractTime)
    ((cap + 1) * (17 * overhead (128 * ((4 * (cap + 1) + 8) * W))) +
      16 * overhead (128 * ((4 * (cap + 1) + 8) * W))) (hh.trans hw) hin
    (by rw [forward_denote]; exact hacc.trans (by dsimp [W, frameWidth]; nlinarith))
    (by rw [reverseList_denote, forward_denote]; exact hrev.trans (by dsimp [W, frameWidth]; nlinarith))
    hfirst (by rw [forward_denote]; exact hreverse)
  rw [expression_eq]
  exact h.trans (by dsimp only [resetTime, W]; omega)

include laws dataLaws in
theorem reset_cost {Γ : List (Ty CryptoAtom)} (tag slot : Nat) (xs : List (TapeCell F))
    (answer : TapeCell F) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width cap counterCap comparisonTime subtractTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hn : ∀ n ≤ counterCap, Q.size rep.data.nat n ≤ width) (hslot : slot ≤ counterCap)
    (htag : Q.size rep.data.nat tag ≤ width)
    (he : Q.size (rep.env (Replay.Mixed.event :: Γ)) (answer, env) ≤ width)
    (hx : ∀ x ∈ xs, Q.size (rep.ty Replay.Mixed.event) x ≤ width) (hc : xs.length ≤ cap)
    (hcompare : ∀ x ∈ xs, (primitiveBound .natEq).time (x.1, tag) ≤ comparisonTime)
    (hzero : ∀ n ≤ counterCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
    (hsub : ∀ n ≤ counterCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (resetCode.weakenTail Γ)) (tag, slot, xs, answer, env) ≤
        resetTime overhead width cap comparisonTime subtractTime :=
  (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound _ _).trans
    (reset_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono tag slot xs answer env
      width cap counterCap comparisonTime subtractTime hh hu hb hn0 hn1 hn hslot htag he hx hc hcompare hzero hsub)

end Signatures.Runtime.Schnorr.SeedTape.NativeReset
