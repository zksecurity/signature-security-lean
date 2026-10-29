import Proofs.Runtime.GeneralSyncWrapFinish
import Proofs.Runtime.GeneralSyncWrapCaps
import Proofs.Runtime.BackendExpressionTime
import Proofs.Runtime.BackendIndexCost
import Proofs.Runtime.BackendReverseCost
import Proofs.Runtime.BackendFoldGrowth
import Proofs.Runtime.BackendListLength

/-! # Cost of the compiled finish

The finish folds over at most `cap` marks; each step looks one coefficient up in the attacker's
coefficient lists, whose lengths are bounded by the encoded output width. Every structural charge
is paid at one frame width bounding every value the finish touches, so the bound is linear in
`cap · outputWidth`. The lemmas are assembled bottom-up from the per-constructor bounds. -/

open PFunctor
open Signatures.Runtime.BackendProgram
open Signatures.Runtime.BackendProgram.Expression (frameFee)

namespace Signatures.Runtime.SyncWrapGeneral

set_option linter.unusedSectionVars false

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
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

/-- Value and operation contracts the finish relies on. -/
structure FinishCaps (width cap opTime : Nat) : Prop where
  hdr : header ≤ width
  unit : Q.size rep.data.unit () ≤ width
  bool : ∀ b, Q.size rep.data.bool b ≤ width
  nat : ∀ k ≤ cap + 1, Q.size rep.data.nat k ≤ width
  scalar : ∀ f : F, Q.size (rep.ty scalar) f ≤ width
  natEq : ∀ k ≤ cap, (primitiveBound CryptoOp.natEq).time (k, 0) ≤ opTime
  natSub : ∀ k ≤ cap, (primitiveBound CryptoOp.natSub).time (k, 1) ≤ opTime
  natAdd : ∀ k ≤ cap, (primitiveBound CryptoOp.natAdd).time (k, 1) ≤ opTime
  zero : (primitiveBound CryptoOp.zero).time () ≤ opTime
  mul : ∀ x y : F, (primitiveBound CryptoOp.mul).time (x, y) ≤ opTime
  neg : ∀ x : F, (primitiveBound CryptoOp.neg).time x ≤ opTime

/-! ## Time budgets, all at a frame width `W` -/

/-- Frame width bounding every value the finish handles: the attacker's output and its
coefficient lists, the marks, the accumulators and the nested environments. -/
def frame (width cap outputWidth : Nat) : Nat :=
  4 * outputWidth + (2 * outputWidth + 16 * cap + 48) * width

/-- One coefficient lookup over a list of length at most `outputWidth`. -/
def lookupTime (overhead : Nat → Nat) (W outputWidth opTime : Nat) : Nat :=
  outputWidth * (2 * opTime + 257 * overhead (128 * W)) + 64 * overhead (128 * W) + opTime +
    31 * frameFee overhead W

/-- One fold step over a mark. -/
def bodyTime (overhead : Nat → Nat) (W outputWidth opTime : Nat) : Nat :=
  2 * lookupTime overhead W outputWidth opTime + 3 * opTime + 72 * frameFee overhead W

/-- Reversing a list of length at most `cap`. -/
def reverseTime (overhead : Nat → Nat) (W cap : Nat) : Nat :=
  cap * (17 * overhead (128 * ((4 * cap + 8) * W))) + 16 * overhead (128 * ((4 * cap + 8) * W))

/-- The fold over at most `cap` marks. -/
def foldTime (overhead : Nat → Nat) (W cap outputWidth opTime : Nat) : Nat :=
  cap * (bodyTime overhead W outputWidth opTime + frameFee overhead W) + 17 * frameFee overhead W

/-- The remapped coefficient list. -/
def coeffsTime (overhead : Nat → Nat) (W cap outputWidth opTime : Nat) : Nat :=
  foldTime overhead W cap outputWidth opTime + 2 * reverseTime overhead W cap + 44 * frameFee overhead W

/-- Appending the negated final scalar. -/
def appendTime (overhead : Nat → Nat) (W cap opTime : Nat) : Nat :=
  reverseTime overhead W cap + opTime + (8 * cap + 23) * frameFee overhead W

/-- The complete finish. -/
def finishTime (overhead : Nat → Nat) (width cap outputWidth opTime : Nat) : Nat :=
  coeffsTime overhead (frame width cap outputWidth) cap outputWidth opTime +
    appendTime overhead (frame width cap outputWidth) cap opTime +
    27 * frameFee overhead (frame width cap outputWidth)

/-! ## Sizes -/

theorem remapMarks_length (γ ξ : List F) (ms : List (Mark F)) (i j : Nat) :
    (remapMarks γ ξ ms i j).length = ms.length := by
  induction ms generalizing i j with
  | nil => rfl
  | cons m rest ih =>
    obtain ⟨flag, c⟩ := m
    cases flag <;> simp [remapMarks, ih]

theorem remapStep_foldl_bounds (γ ξ : List F) (ms : List (Mark F)) (acc : List F × Nat × Nat) :
    (ms.foldl (remapStep γ ξ) acc).1.length ≤ acc.1.length + ms.length ∧
    (ms.foldl (remapStep γ ξ) acc).2.1 ≤ acc.2.1 + ms.length ∧
    (ms.foldl (remapStep γ ξ) acc).2.2 ≤ acc.2.2 + ms.length := by
  induction ms generalizing acc with
  | nil => simp
  | cons m rest ih =>
    obtain ⟨flag, c⟩ := m
    have h := ih (remapStep γ ξ acc (flag, c))
    cases flag <;>
      simp only [List.foldl_cons, remapStep, Bool.false_eq_true, ite_false, ite_true, List.length_cons] at h ⊢ <;>
      omega

theorem foldl_cons_eq {α : Type} (xs acc : List α) :
    xs.foldl (fun acc x => x :: acc) acc = xs.reverse ++ acc := by
  have h := foldl_cons_reverse xs.reverse acc
  rwa [List.reverse_reverse] at h

include sizes lists

theorem scalars_size (width n : Nat) (hh : header ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ys : List F) (hl : ys.length ≤ n) : Q.size (rep.ty (.list scalar)) ys ≤ (2 * n + 1) * width := by
  have h := lists.size_le_cap (rep.ty scalar) ys width n (fun f _ => hf f) hl
  change Q.size (rep.ty (.list scalar)) ys ≤ _ at h
  nlinarith [Nat.mul_le_mul_left n hh]

theorem acc_size (width n : Nat) (hh : header ≤ width)
    (hn : ∀ k ≤ n, Q.size rep.data.nat k ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (acc : List F × Nat × Nat) (hl : acc.1.length ≤ n) (hi : acc.2.1 ≤ n) (hj : acc.2.2 ≤ n) :
    Q.size (rep.ty accTy) acc ≤ (2 * n + 5) * width := by
  have hout := scalars_size rep sizes lists width n hh hf acc.1 hl
  have h1 := sizes.prod_le (rep.ty (.list scalar)) (rep.ty (.pair .nat .nat)) acc
  have h2 := sizes.prod_le rep.data.nat rep.data.nat acc.2
  have hi' := hn acc.2.1 hi
  have hj' := hn acc.2.2 hj
  change Q.size (rep.ty accTy) acc ≤ _ at h1
  change Q.size (rep.ty (.pair .nat .nat)) acc.2 ≤ _ at h2
  nlinarith

theorem natPair_size (width : Nat) (hh : header ≤ width) (x y : Nat)
    (hx : Q.size rep.data.nat x ≤ width) (hy : Q.size rep.data.nat y ≤ width) :
    Q.size (rep.ty (.pair .nat .nat)) (x, y) ≤ 3 * width := by
  have h := sizes.prod_le rep.data.nat rep.data.nat (x, y)
  dsimp only at h
  change Q.size (rep.ty (.pair .nat .nat)) (x, y) ≤ _ at h
  omega

/-! ## Times -/

include mono

local notation "arith" => arithmetic F G₁ G₂ K M cost
local notation "bound" e =>
  Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound e
local notation "VAR" =>
  Expression.var_time rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes mono
local notation "UNIT" =>
  Expression.unit_time rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes mono
local notation "NATC" =>
  Expression.nat_time rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes mono
local notation "PAIR" =>
  Expression.pair_time rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes mono
local notation "FST" =>
  Expression.fst_time rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes mono
local notation "SND" =>
  Expression.snd_time rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes mono
local notation "NIL" =>
  Expression.nil_time rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes lists mono
local notation "CONS" =>
  Expression.cons_time rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes lists mono
local notation "LETE" =>
  Expression.letE_time rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes mono
local notation "OPT" =>
  Expression.op_time rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes mono
local notation "BRANCH" =>
  Expression.branch_time rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes mono
local notation "FOLD" =>
  Expression.fold_time rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes mono

variable {Γ : List (Ty CryptoAtom)} {width cap outputWidth opTime : Nat}
  (caps : FinishCaps (header := header) rep cost primitive primitiveBound width cap opTime)

include caps

omit caps in
/-- Variables are read at the frame. -/
theorem var_depth_time {a} (v : Var Γ a) (env : Env (cryptoBase F G₁ G₂ K M) Γ) (W d : Nat)
    (henv : Q.size (rep.env Γ) env ≤ W) (hd : v.depth = d) :
    (bound (.var v : Expr CryptoOp Γ a)).time env ≤ (2 * d + 1) * frameFee overhead W := by
  subst hd
  exact VAR v env W henv

omit caps in
theorem env_cons_size {a} (x : a.Value (cryptoBase F G₁ G₂ K M)) (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    Q.size (rep.env (a :: Γ)) (x, env) ≤ Q.size (rep.ty a) x + Q.size (rep.env Γ) env + header :=
  sizes.prod_le (rep.ty a) (rep.env Γ) (x, env)

/-- One coefficient lookup, with the whole body frame retained. -/
theorem lookupSign_time (m : Mark F) (acc : List F × Nat × Nat) (marks : List (Mark F)) (γ ξ : List F)
    (tail : Env (cryptoBase F G₁ G₂ K M) Γ) (W : Nat) (hw : width ≤ W)
    (hB : Q.size (rep.env (bodyEnv Γ)) (m, acc, marks, γ, ξ, tail) + outputWidth + 6 * width ≤ W)
    (hξ : Q.size (rep.ty (.list scalar)) ξ ≤ outputWidth) (hξc : ξ.length ≤ outputWidth) (hj : acc.2.2 ≤ cap)
    (hlist : ∀ ys : List F, ys.length ≤ outputWidth → Q.size (rep.ty (.list scalar)) ys ≤ W) :
    (bound (lookupSign (Γ := Γ))).time (m, acc, marks, γ, ξ, tail) ≤ lookupTime overhead W outputWidth opTime := by
  obtain ⟨hh, hu, hb, hn, hf, hEq, hSub, hAdd, hZero, hMul, hNeg⟩ := caps
  have hhW : header ≤ W := by omega
  have hB' : Q.size (rep.env (bodyEnv Γ)) (m, acc, marks, γ, ξ, tail) ≤ W := by omega
  have hacc : Q.size (rep.ty accTy) acc ≤ Q.size (rep.env (bodyEnv Γ)) (m, acc, marks, γ, ξ, tail) :=
    Expression.var_size rep sizes (Var.there .here : Var (bodyEnv Γ) accTy) (m, acc, marks, γ, ξ, tail)
  have hacc2 := sizes.snd_le (rep.ty (.list scalar)) (rep.ty (.pair .nat .nat)) acc
  have hE1 := env_cons_size rep sizes lists mono (a := .list scalar) (Γ := bodyEnv Γ) ξ (m, acc, marks, γ, ξ, tail)
  have hE2 := env_cons_size rep sizes lists mono (a := scalar) (Γ := .list scalar :: bodyEnv Γ)
    ((arith).execute CryptoOp.zero ()) (ξ, m, acc, marks, γ, ξ, tail)
  have hz := hf ((arith).execute CryptoOp.zero ())
  have hidx := IndexCompiler.index_time_bound_of_caps rep data arith primitive laws dataLaws primitiveBound sizes mono
    (cell := scalar) (Γ := bodyEnv Γ) CryptoOp.natEq CryptoOp.natSub (fun _ _ => rfl) (fun _ _ => rfl)
    acc.2.2 ((arith).execute CryptoOp.zero ()) ξ (m, acc, marks, γ, ξ, tail) W opTime opTime outputWidth
    hhW (hu.trans hw) hB' (fun b => (hb b).trans hw)
    (fun k hk => (hn k (by omega)).trans hw) ((hn 1 (by omega)).trans hw) (hz.trans hw)
    (fun f _ => (hf f).trans hw) hξc (fun ys hys _ => hlist ys hys)
    (fun k hk => hEq k (by omega)) (fun k hk => hSub k (by omega))
  dsimp only [lookupSign]
  -- the innermost let binds the signing count
  have hE1' : Q.size (rep.env (.list scalar :: bodyEnv Γ)) (ξ, m, acc, marks, γ, ξ, tail) ≤ W := by omega
  have hE2' : Q.size (rep.env (scalar :: .list scalar :: bodyEnv Γ))
      ((arith).execute CryptoOp.zero (), ξ, m, acc, marks, γ, ξ, tail) ≤ W := by omega
  have t3v := var_depth_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Var.there (.there (.there .here)) : Var (scalar :: .list scalar :: bodyEnv Γ) accTy) _ W 3 hE2' rfl
  have t3s := SND _ _ W _ hE2' (by exact hacc.trans hB') t3v
  have t3 := SND _ _ W _ hE2' (by exact (hacc2.trans hacc).trans hB') t3s
  have L3 := LETE _ _ _ W _ _ hhW hE2' (by exact (hn acc.2.2 (by omega)).trans hw) (by exact (hf _).trans hw) t3 hidx
  have t2u := UNIT _ W hE1' (hu.trans hw)
  have t2 := OPT CryptoOp.zero _ _ W _ _ hE1' (by exact hu.trans hw) (by exact hz.trans hw) t2u (by exact hZero)
  have L2 := LETE _ _ _ W _ _ hhW hE1' (by exact hz.trans hw) (by exact (hf _).trans hw) t2 L3
  have t1 := var_depth_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Var.there (.there (.there (.there .here))) : Var (bodyEnv Γ) (.list scalar)) _ W 4 hB' rfl
  have L1 := LETE _ _ _ W _ _ hhW hB' (by show Q.size (rep.ty (.list scalar)) ξ ≤ W; omega)
    (by exact (hf _).trans hw) t1 L2
  dsimp only [lookupTime]
  linarith

theorem lookupHash_time (m : Mark F) (acc : List F × Nat × Nat) (marks : List (Mark F)) (γ ξ : List F)
    (tail : Env (cryptoBase F G₁ G₂ K M) Γ) (W : Nat) (hw : width ≤ W)
    (hB : Q.size (rep.env (bodyEnv Γ)) (m, acc, marks, γ, ξ, tail) + outputWidth + 6 * width ≤ W)
    (hγ : Q.size (rep.ty (.list scalar)) γ ≤ outputWidth) (hγc : γ.length ≤ outputWidth) (hi : acc.2.1 ≤ cap)
    (hlist : ∀ ys : List F, ys.length ≤ outputWidth → Q.size (rep.ty (.list scalar)) ys ≤ W) :
    (bound (lookupHash (Γ := Γ))).time (m, acc, marks, γ, ξ, tail) ≤ lookupTime overhead W outputWidth opTime := by
  obtain ⟨hh, hu, hb, hn, hf, hEq, hSub, hAdd, hZero, hMul, hNeg⟩ := caps
  have hhW : header ≤ W := by omega
  have hB' : Q.size (rep.env (bodyEnv Γ)) (m, acc, marks, γ, ξ, tail) ≤ W := by omega
  have hacc : Q.size (rep.ty accTy) acc ≤ Q.size (rep.env (bodyEnv Γ)) (m, acc, marks, γ, ξ, tail) :=
    Expression.var_size rep sizes (Var.there .here : Var (bodyEnv Γ) accTy) (m, acc, marks, γ, ξ, tail)
  have hacc2 := sizes.snd_le (rep.ty (.list scalar)) (rep.ty (.pair .nat .nat)) acc
  have hE1 := env_cons_size rep sizes lists mono (a := .list scalar) (Γ := bodyEnv Γ) γ (m, acc, marks, γ, ξ, tail)
  have hE2 := env_cons_size rep sizes lists mono (a := scalar) (Γ := .list scalar :: bodyEnv Γ)
    ((arith).execute CryptoOp.zero ()) (γ, m, acc, marks, γ, ξ, tail)
  have hz := hf ((arith).execute CryptoOp.zero ())
  have hidx := IndexCompiler.index_time_bound_of_caps rep data arith primitive laws dataLaws primitiveBound sizes mono
    (cell := scalar) (Γ := bodyEnv Γ) CryptoOp.natEq CryptoOp.natSub (fun _ _ => rfl) (fun _ _ => rfl)
    acc.2.1 ((arith).execute CryptoOp.zero ()) γ (m, acc, marks, γ, ξ, tail) W opTime opTime outputWidth
    hhW (hu.trans hw) hB' (fun b => (hb b).trans hw)
    (fun k hk => (hn k (by omega)).trans hw) ((hn 1 (by omega)).trans hw) (hz.trans hw)
    (fun f _ => (hf f).trans hw) hγc (fun ys hys _ => hlist ys hys)
    (fun k hk => hEq k (by omega)) (fun k hk => hSub k (by omega))
  dsimp only [lookupHash]
  have hE1' : Q.size (rep.env (.list scalar :: bodyEnv Γ)) (γ, m, acc, marks, γ, ξ, tail) ≤ W := by omega
  have hE2' : Q.size (rep.env (scalar :: .list scalar :: bodyEnv Γ))
      ((arith).execute CryptoOp.zero (), γ, m, acc, marks, γ, ξ, tail) ≤ W := by omega
  have t3v := var_depth_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Var.there (.there (.there .here)) : Var (scalar :: .list scalar :: bodyEnv Γ) accTy) _ W 3 hE2' rfl
  have t3s := SND _ _ W _ hE2' (by exact hacc.trans hB') t3v
  have t3 := FST _ _ W _ hE2' (by exact (hacc2.trans hacc).trans hB') t3s
  have L3 := LETE _ _ _ W _ _ hhW hE2' (by exact (hn acc.2.1 (by omega)).trans hw) (by exact (hf _).trans hw) t3 hidx
  have t2u := UNIT _ W hE1' (hu.trans hw)
  have t2 := OPT CryptoOp.zero _ _ W _ _ hE1' (by exact hu.trans hw) (by exact hz.trans hw) t2u (by exact hZero)
  have L2 := LETE _ _ _ W _ _ hhW hE1' (by exact hz.trans hw) (by exact (hf _).trans hw) t2 L3
  have t1 := var_depth_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Var.there (.there (.there .here)) : Var (bodyEnv Γ) (.list scalar)) _ W 3 hB' rfl
  have L1 := LETE _ _ _ W _ _ hhW hB' (by show Q.size (rep.ty (.list scalar)) γ ≤ W; omega)
    (by exact (hf _).trans hw) t1 L2
  dsimp only [lookupTime]
  linarith

/-- One fold step over a mark. -/
theorem remapBody_time (m : Mark F) (acc : List F × Nat × Nat) (marks : List (Mark F)) (γ ξ : List F)
    (tail : Env (cryptoBase F G₁ G₂ K M) Γ) (W : Nat) (hw : width ≤ W)
    (hB : Q.size (rep.env (bodyEnv Γ)) (m, acc, marks, γ, ξ, tail) + outputWidth + 6 * width ≤ W)
    (hcap : (2 * cap + 7) * width ≤ W)
    (hγ : Q.size (rep.ty (.list scalar)) γ ≤ outputWidth) (hξ : Q.size (rep.ty (.list scalar)) ξ ≤ outputWidth)
    (hγc : γ.length ≤ outputWidth) (hξc : ξ.length ≤ outputWidth)
    (hl : acc.1.length ≤ cap) (hi : acc.2.1 ≤ cap) (hj : acc.2.2 ≤ cap)
    (hlist : ∀ ys : List F, ys.length ≤ outputWidth → Q.size (rep.ty (.list scalar)) ys ≤ W) :
    (bound (remapBody (Γ := Γ))).time (m, acc, marks, γ, ξ, tail) ≤ bodyTime overhead W outputWidth opTime := by
  have hS := lookupSign_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono caps
    m acc marks γ ξ tail W hw hB hξ hξc hj hlist
  have hH := lookupHash_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono caps
    m acc marks γ ξ tail W hw hB hγ hγc hi hlist
  obtain ⟨hh, hu, hb, hn, hf, hEq, hSub, hAdd, hZero, hMul, hNeg⟩ := caps
  have hhW : header ≤ W := by omega
  have hB' : Q.size (rep.env (bodyEnv Γ)) (m, acc, marks, γ, ξ, tail) ≤ W := by omega
  have hm : Q.size (rep.ty markTy) m ≤ Q.size (rep.env (bodyEnv Γ)) (m, acc, marks, γ, ξ, tail) :=
    Expression.var_size rep sizes (Var.here : Var (bodyEnv Γ) markTy) (m, acc, marks, γ, ξ, tail)
  have hacc : Q.size (rep.ty accTy) acc ≤ Q.size (rep.env (bodyEnv Γ)) (m, acc, marks, γ, ξ, tail) :=
    Expression.var_size rep sizes (Var.there .here : Var (bodyEnv Γ) accTy) (m, acc, marks, γ, ξ, tail)
  have hacc1 := sizes.fst_le (rep.ty (.list scalar)) (rep.ty (.pair .nat .nat)) acc
  have hacc2 := sizes.snd_le (rep.ty (.list scalar)) (rep.ty (.pair .nat .nat)) acc
  have hscalars : ∀ x y : F, Q.size (rep.ty (.pair scalar scalar)) (x, y) ≤ W := fun x y => by
    have h := sizes.prod_le (rep.ty scalar) (rep.ty scalar) (x, y)
    have hx := hf x; have hy := hf y
    dsimp only at h
    change Q.size (rep.ty (.pair scalar scalar)) (x, y) ≤ _ at h
    omega
  have hnats : ∀ x y : Nat, x ≤ cap + 1 → y ≤ cap + 1 → Q.size (rep.ty (.pair .nat .nat)) (x, y) ≤ W :=
    fun x y hx hy => by
      have h := sizes.prod_le rep.data.nat rep.data.nat (x, y)
      have hx' := hn x hx; have hy' := hn y hy
      dsimp only at h
      change Q.size (rep.ty (.pair .nat .nat)) (x, y) ≤ _ at h
      omega
  have hres : ∀ (xs : List F) (i j : Nat), xs.length ≤ cap + 1 → i ≤ cap + 1 → j ≤ cap + 1 →
      Q.size (rep.ty accTy) (xs, i, j) ≤ W := fun xs i j h1 h2 h3 =>
    (acc_size rep sizes lists width (cap + 1) hh hn hf (xs, i, j) h1 h2 h3).trans hcap
  have hcons : ∀ x : F, Q.size (rep.ty (.list scalar)) (x :: acc.1) ≤ W := fun x => by
    have := scalars_size rep sizes lists width (cap + 1) hh hf (x :: acc.1) (by simp; omega)
    nlinarith
  dsimp only [remapBody]
  -- pieces in the body environment
  have tv0 := var_depth_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Var.here : Var (bodyEnv Γ) markTy) _ W 0 hB' rfl
  have tv1 := var_depth_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Var.there .here : Var (bodyEnv Γ) accTy) _ W 1 hB' rfl
  have tc := FST _ _ W _ hB' (by exact hm.trans hB') tv0
  have ts0 := SND _ _ W _ hB' (by exact hm.trans hB') tv0
  have tf1 := FST _ _ W _ hB' (by exact hacc.trans hB') tv1
  have ts1 := SND _ _ W _ hB' (by exact hacc.trans hB') tv1
  have tfs1 := FST _ _ W _ hB' (by exact (hacc2.trans hacc).trans hB') ts1
  have tss1 := SND _ _ W _ hB' (by exact (hacc2.trans hacc).trans hB') ts1
  have tn1 := NATC 1 _ W hB' (hu.trans hw) ((hn 1 (by omega)).trans hw)
  -- yes branch
  have tp1 := PAIR _ _ _ W _ _ hhW hB' (by exact (hf _).trans hw) (by exact (hf _).trans hw) hS ts0
  have to1 := OPT CryptoOp.mul _ _ W _ _ hB' (by exact hscalars _ _) (by exact (hf _).trans hw) tp1 (by exact hMul _ _)
  have tc1 := CONS _ _ _ W _ _ hhW hB' (by exact (hf _).trans hw) (by exact (hacc1.trans hacc).trans hB') to1 tf1
  have tp2 := PAIR _ _ _ W _ _ hhW hB' (by exact (hn acc.2.2 (by omega)).trans hw) (by exact (hn 1 (by omega)).trans hw) tss1 tn1
  have to2 := OPT CryptoOp.natAdd _ _ W _ _ hB'
    (by show Q.size (rep.ty (.pair .nat .nat)) (acc.2.2, 1) ≤ W; exact hnats _ _ (by omega) (by omega))
    (by show Q.size rep.data.nat (acc.2.2 + 1) ≤ W; exact (hn _ (by omega)).trans hw) tp2 (by exact hAdd _ hj)
  have tp3 := PAIR _ _ _ W _ _ hhW hB' (by exact (hn acc.2.1 (by omega)).trans hw)
    (by show Q.size rep.data.nat (acc.2.2 + 1) ≤ W; exact (hn _ (by omega)).trans hw) tfs1 to2
  have tyes := PAIR _ _ _ W _ _ hhW hB' (by exact hcons _)
    (by show Q.size (rep.ty (.pair .nat .nat)) (acc.2.1, acc.2.2 + 1) ≤ W; exact hnats _ _ (by omega) (by omega)) tc1 tp3
  -- no branch
  have tc2 := CONS _ _ _ W _ _ hhW hB' (by exact (hf _).trans hw) (by exact (hacc1.trans hacc).trans hB') hH tf1
  have tp4 := PAIR _ _ _ W _ _ hhW hB' (by exact (hn acc.2.1 (by omega)).trans hw) (by exact (hn 1 (by omega)).trans hw) tfs1 tn1
  have to3 := OPT CryptoOp.natAdd _ _ W _ _ hB'
    (by show Q.size (rep.ty (.pair .nat .nat)) (acc.2.1, 1) ≤ W; exact hnats _ _ (by omega) (by omega))
    (by show Q.size rep.data.nat (acc.2.1 + 1) ≤ W; exact (hn _ (by omega)).trans hw) tp4 (by exact hAdd _ hi)
  have tp5 := PAIR _ _ _ W _ _ hhW hB' (by show Q.size rep.data.nat (acc.2.1 + 1) ≤ W; exact (hn _ (by omega)).trans hw)
    (by exact (hn acc.2.2 (by omega)).trans hw) to3 tss1
  have tno := PAIR _ _ _ W _ _ hhW hB' (by exact hcons _)
    (by show Q.size (rep.ty (.pair .nat .nat)) (acc.2.1 + 1, acc.2.2) ≤ W; exact hnats _ _ (by omega) (by omega)) tc2 tp5
  have tb := BRANCH _ _ _ _ W _ _ _ hhW hB' (fun b => (hb b).trans hw)
    (by
      show Q.size (rep.ty accTy) (_ :: acc.1, acc.2.1, acc.2.2 + 1) ≤ W
      exact hres _ _ _ (by simp only [List.length_cons]; omega) (by omega) (by omega))
    (by
      show Q.size (rep.ty accTy) (_ :: acc.1, acc.2.1 + 1, acc.2.2) ≤ W
      exact hres _ _ _ (by simp only [List.length_cons]; omega) (by omega) (by omega))
    tc tyes tno
  dsimp only [bodyTime]
  linarith

/-- The fold over the marks. -/
theorem remapFold_time (ms : List (Mark F)) (γ ξ : List F) (tail : Env (cryptoBase F G₁ G₂ K M) Γ) (W : Nat)
    (hw : width ≤ W) (hms : ms.length ≤ cap)
    (hE : Q.size (rep.env (remapEnv Γ)) (ms, γ, ξ, tail) + marksWidth width cap + (2 * cap + 5) * width +
      outputWidth + 16 * width ≤ W)
    (hγ : Q.size (rep.ty (.list scalar)) γ ≤ outputWidth) (hξ : Q.size (rep.ty (.list scalar)) ξ ≤ outputWidth)
    (hγc : γ.length ≤ outputWidth) (hξc : ξ.length ≤ outputWidth)
    (hlist : ∀ ys : List F, ys.length ≤ outputWidth → Q.size (rep.ty (.list scalar)) ys ≤ W) :
    (bound (remapFold (Γ := Γ))).time (ms, γ, ξ, tail) ≤ foldTime overhead W cap outputWidth opTime := by
  have hbody := remapBody_time (Γ := Γ) (outputWidth := outputWidth) rep data cost primitive laws dataLaws
    primitiveBound sizes lists mono caps
  obtain ⟨hh, hu, hb, hn, hf, hEq, hSub, hAdd, hZero, hMul, hNeg⟩ := caps
  have hhW : header ≤ W := by omega
  have hE' : Q.size (rep.env (remapEnv Γ)) (ms, γ, ξ, tail) ≤ W := by omega
  have hms' : Q.size (rep.ty (.list markTy)) ms ≤ Q.size (rep.env (remapEnv Γ)) (ms, γ, ξ, tail) :=
    Expression.var_size rep sizes (Var.here : Var (remapEnv Γ) (.list markTy)) (ms, γ, ξ, tail)
  have hmark : ∀ x : Mark F, Q.size (rep.ty markTy) x ≤ 3 * width := mark_size rep sizes lists width hh hb hf
  have hmarks : ∀ xs : List (Mark F), xs.length ≤ cap → Q.size (rep.ty (.list markTy)) xs ≤ marksWidth width cap :=
    fun xs hxs => marks_size rep sizes lists width cap hh hb hf xs hxs
  have haccW : ∀ acc : List F × Nat × Nat, acc.1.length ≤ cap → acc.2.1 ≤ cap → acc.2.2 ≤ cap →
      Q.size (rep.ty accTy) acc ≤ (2 * cap + 5) * width := fun acc h1 h2 h3 =>
    acc_size rep sizes lists width cap hh (fun k hk => hn k (by omega)) hf acc h1 h2 h3
  have hcap : (2 * cap + 7) * width ≤ W := by
    have : (2 * cap + 7) * width = (2 * cap + 5) * width + 2 * width := by ring
    omega
  have hstep : ∀ acc x, remapBody.denote arith (x, acc, ms, γ, ξ, tail) = remapStep γ ξ acc x :=
    fun acc x => remapBody_denote cost x acc ms γ ξ tail
  have hfoldres : ∀ xs : List (Mark F), ∀ acc : List F × Nat × Nat, acc.1.length + xs.length ≤ cap →
      acc.2.1 + xs.length ≤ cap → acc.2.2 + xs.length ≤ cap →
      Q.size (rep.ty accTy) (xs.foldl (remapStep γ ξ) acc) ≤ (2 * cap + 5) * width := by
    intro xs acc h1 h2 h3
    obtain ⟨b1, b2, b3⟩ := remapStep_foldl_bounds γ ξ xs acc
    exact haccW _ (by omega) (by omega) (by omega)
  have hbodyEnv : ∀ (x : Mark F) (acc : List F × Nat × Nat), acc.1.length ≤ cap → acc.2.1 ≤ cap → acc.2.2 ≤ cap →
      Q.size (rep.env (bodyEnv Γ)) (x, acc, ms, γ, ξ, tail) + outputWidth + 6 * width ≤ W := by
    intro x acc h1 h2 h3
    have e1 := env_cons_size rep sizes lists mono (a := accTy) (Γ := remapEnv Γ) acc (ms, γ, ξ, tail)
    have e2 := env_cons_size rep sizes lists mono (a := markTy) (Γ := accTy :: remapEnv Γ) x (acc, ms, γ, ξ, tail)
    have := hmark x
    have := haccW acc h1 h2 h3
    change Q.size (rep.env (bodyEnv Γ)) (x, acc, ms, γ, ξ, tail) ≤ _ at e2
    omega
  dsimp only [remapFold]
  have txs := var_depth_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Var.here : Var (remapEnv Γ) (.list markTy)) _ W 0 hE' rfl
  have tn0 := NATC 0 _ W hE' (hu.trans hw) ((hn 0 (by omega)).trans hw)
  have tnil : (bound (.nil : Expr CryptoOp (remapEnv Γ) (.list scalar))).time (ms, γ, ξ, tail) ≤
      3 * frameFee overhead W := NIL _ W hhW hE' (hu.trans hw)
  have tpn := PAIR _ _ _ W _ _ hhW hE' (by exact (hn 0 (by omega)).trans hw) (by exact (hn 0 (by omega)).trans hw) tn0 tn0
  have tinit := PAIR _ _ _ W _ _ hhW hE' (by exact (lists.nil_le _).trans hhW)
    (by
      show Q.size (rep.ty (.pair .nat .nat)) (0, 0) ≤ W
      exact (natPair_size rep sizes lists width hh 0 0 (hn 0 (by omega)) (hn 0 (by omega))).trans (by omega))
    tnil tpn
  have twork := foldWork_bound_remaining
    (fun x acc => remapBody.denote arith (x, acc, ms, γ, ξ, tail))
    (fun x acc => (bound (remapBody (Γ := Γ))).time (x, acc, ms, γ, ξ, tail))
    (foldFee (Q := Q) overhead rep.data (rep.ty markTy) (rep.ty accTy) (rep.env (remapEnv Γ))
      (remapBody.denote arith) (ms, γ, ξ, tail))
    (fun _ => True)
    (fun remaining (acc : List F × Nat × Nat) =>
      acc.1.length + remaining ≤ cap ∧ acc.2.1 + remaining ≤ cap ∧ acc.2.2 + remaining ≤ cap)
    (bodyTime overhead W outputWidth opTime) (frameFee overhead W) cap
    (by
      intro remaining hrem x _ (acc : List F × Nat × Nat) hinv
      obtain ⟨h1, h2, h3⟩ := hinv
      try dsimp only at h1 h2 h3
      refine ⟨hbody x acc ms γ ξ tail W hw (hbodyEnv x acc (by omega) (by omega) (by omega)) hcap
        hγ hξ hγc hξc (by omega) (by omega) (by omega) hlist, ?_⟩
      show (remapBody.denote arith (x, acc, ms, γ, ξ, tail)).1.length + remaining ≤ cap ∧ _
      rw [hstep]
      dsimp only [remapStep]
      split <;> simp only [List.length_cons] <;> omega)
    (by
      intro xs hxs _ (acc : List F × Nat × Nat) hinv
      obtain ⟨h1, h2, h3⟩ := hinv
      try dsimp only at h1 h2 h3
      unfold foldFee
      apply mono
      have hres := hfoldres xs acc h1 h2 h3
      have e1 := env_cons_size rep sizes lists mono (a := accTy) (Γ := remapEnv Γ) acc (ms, γ, ξ, tail)
      have e2 := env_cons_size rep sizes lists mono (a := .list markTy) (Γ := accTy :: remapEnv Γ) xs
        (acc, ms, γ, ξ, tail)
      have := hmarks xs hxs
      have := haccW acc (by omega) (by omega) (by omega)
      simp only [hstep]
      change Q.size (rep.env (.list markTy :: accTy :: remapEnv Γ)) (xs, acc, ms, γ, ξ, tail) +
        Q.size (rep.ty accTy) (xs.foldl (remapStep γ ξ) acc) ≤ 16 * W
      omega)
    ms hms (fun _ _ => trivial) ([], 0, 0) ⟨by simpa using hms, by simpa using hms, by simpa using hms⟩
  have tf := FOLD _ _ _ _ W _ _ _ hhW hE' (by exact hms'.trans hE')
    (by exact (haccW ([], 0, 0) (by simp) (Nat.zero_le _) (Nat.zero_le _)).trans (by omega))
    (by
      simp only [hstep]
      change Q.size (rep.ty accTy) (ms.foldl (remapStep γ ξ) ([], 0, 0)) ≤ W
      exact (hfoldres ms ([], 0, 0) (by simpa using hms) (by simpa using hms) (by simpa using hms)).trans (by omega))
    txs tinit (twork.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hms) _))
  dsimp only [foldTime]
  linarith

/-- The remapped coefficient list, in order. -/
theorem remapExpr_time (ms : List (Mark F)) (γ ξ : List F) (tail : Env (cryptoBase F G₁ G₂ K M) Γ) (W : Nat)
    (hw : width ≤ W) (hms : ms.length ≤ cap)
    (hE : Q.size (rep.env (remapEnv Γ)) (ms, γ, ξ, tail) + marksWidth width cap + (2 * cap + 5) * width +
      outputWidth + 16 * width ≤ W)
    (hγ : Q.size (rep.ty (.list scalar)) γ ≤ outputWidth) (hξ : Q.size (rep.ty (.list scalar)) ξ ≤ outputWidth)
    (hγc : γ.length ≤ outputWidth) (hξc : ξ.length ≤ outputWidth)
    (hlist : ∀ ys : List F, ys.length ≤ outputWidth → Q.size (rep.ty (.list scalar)) ys ≤ W) :
    (bound (remapExpr (Γ := Γ))).time (ms, γ, ξ, tail) ≤
      foldTime overhead W cap outputWidth opTime + reverseTime overhead W cap + 9 * frameFee overhead W := by
  have tfold := remapFold_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono caps
    ms γ ξ tail W hw hms hE hγ hξ hγc hξc hlist
  obtain ⟨hh, hu, hb, hn, hf, hEq, hSub, hAdd, hZero, hMul, hNeg⟩ := caps
  have hhW : header ≤ W := by omega
  have hE' : Q.size (rep.env (remapEnv Γ)) (ms, γ, ξ, tail) ≤ W := by omega
  have hfold : remapFold.denote arith (ms, γ, ξ, tail) = ms.foldl (remapStep γ ξ) ([], 0, 0) :=
    remapFold_denote cost ms γ ξ tail
  obtain ⟨b1, b2, b3⟩ := remapStep_foldl_bounds γ ξ ms ([], 0, 0)
  simp only [List.length_nil, Nat.zero_add] at b1 b2 b3
  have haccS : Q.size (rep.ty accTy) (ms.foldl (remapStep γ ξ) ([], 0, 0)) ≤ (2 * cap + 5) * width :=
    acc_size rep sizes lists width cap hh (fun k hk => hn k (by omega)) hf _ (by omega) (by omega) (by omega)
  have hcoeffs : Q.size (rep.ty (.list scalar)) (ms.foldl (remapStep γ ξ) ([], 0, 0)).1 ≤ (2 * cap + 1) * width :=
    scalars_size rep sizes lists width cap hh hf _ (by omega)
  have hcoeffsR : Q.size (rep.ty (.list scalar)) (ms.foldl (remapStep γ ξ) ([], 0, 0)).1.reverse ≤
      (2 * cap + 1) * width :=
    scalars_size rep sizes lists width cap hh hf _ (by rw [List.length_reverse]; omega)
  have hE4 := env_cons_size rep sizes lists mono (a := accTy) (Γ := remapEnv Γ)
    (ms.foldl (remapStep γ ξ) ([], 0, 0)) (ms, γ, ξ, tail)
  have hE4' : Q.size (rep.env (accTy :: remapEnv Γ)) (ms.foldl (remapStep γ ξ) ([], 0, 0), ms, γ, ξ, tail) ≤ W := by
    omega
  have hsmall : (2 * cap + 1) * width ≤ W := by
    have : (2 * cap + 5) * width = (2 * cap + 1) * width + 4 * width := by ring
    omega
  dsimp only [remapExpr]
  have tv := var_depth_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Var.here : Var (accTy :: remapEnv Γ) accTy) _ W 0 hE4' rfl
  have tfst := FST _ _ W _ hE4' (by exact haccS.trans (by omega)) tv
  have trev := ReverseCompiler.reverse_time_bound rep data arith primitive laws dataLaws primitiveBound sizes lists mono
    (cell := scalar) (Γ := accTy :: remapEnv Γ) (ms.foldl (remapStep γ ξ) ([], 0, 0)).1
    (ms.foldl (remapStep γ ξ) ([], 0, 0), ms, γ, ξ, tail) W cap hhW (hu.trans hw) hE4'
    (fun x _ => (hf x).trans hw) (by omega)
  have Lin := LETE _ _ _ W _ _ hhW hE4' (by exact hcoeffs.trans hsmall)
    (by rw [reverseList_denote]; exact hcoeffsR.trans hsmall) tfst (by exact trev)
  have Lout := LETE _ _ _ W _ _ hhW hE' (by rw [hfold]; exact haccS.trans (by omega))
    (by
      change Q.size (rep.ty (.list scalar)) (remapExpr.denote arith (ms, γ, ξ, tail)) ≤ W
      rw [remapExpr_denote]
      exact (scalars_size rep sizes lists width cap hh hf _ (by simpa [remapMarks_length] using hms)).trans hsmall)
    tfold (by rewrite [hfold]; exact Lin)
  dsimp only [reverseTime] at *
  linarith

/-- The finish environment: the attacker's output, the marks and the final scalar. -/
abbrev finishEnv : List (Ty CryptoAtom) := [OutTy, .list markTy, scalar]

omit sizes lists mono caps in
/-- The frame, written over the product atoms `outputWidth · width` and `cap · width`. -/
theorem frame_eq (width cap outputWidth : Nat) :
    frame width cap outputWidth = 4 * outputWidth + 2 * (outputWidth * width) + 16 * (cap * width) + 48 * width := by
  unfold frame; ring

omit sizes lists mono caps in
theorem marksWidth_eq (width cap : Nat) : marksWidth width cap = 4 * (cap * width) + width := by
  unfold marksWidth; ring

/-- The common facts about the finish inputs. -/
theorem finish_facts (lens : ListLengthLaws Q rep.data) (r : OutTy.Value (cryptoBase F G₁ G₂ K M))
    (marks : List (Mark F)) (v : F) (hr : Q.size (rep.ty OutTy) r ≤ outputWidth) (hmarks : marks.length ≤ cap) :
    Q.size (rep.ty Weights.syncMessage) r.1 ≤ outputWidth ∧
    Q.size (rep.ty scalar) r.2.1 ≤ outputWidth ∧
    Q.size (rep.ty (.list scalar)) r.2.2.1 ≤ outputWidth ∧ Q.size (rep.ty (.list scalar)) r.2.2.2 ≤ outputWidth ∧
    r.2.2.1.length ≤ outputWidth ∧ r.2.2.2.length ≤ outputWidth ∧
    Q.size (rep.ty (.list markTy)) marks ≤ marksWidth width cap ∧
    Q.size (rep.ty (.list markTy)) marks.reverse ≤ marksWidth width cap ∧
    Q.size (rep.env finishEnv) (r, marks, v, ()) ≤ outputWidth + marksWidth width cap + 5 * width := by
  obtain ⟨hh, hu, hb, hn, hf, hEq, hSub, hAdd, hZero, hMul, hNeg⟩ := caps
  have hr1 : Q.size (rep.ty Weights.syncMessage) r.1 ≤ Q.size (rep.ty OutTy) r := sizes.fst_le _ _ r
  have hr2 : Q.size (rep.ty (.pair scalar (.pair (.list scalar) (.list scalar)))) r.2 ≤ Q.size (rep.ty OutTy) r :=
    sizes.snd_le _ _ r
  have hr21 : Q.size (rep.ty scalar) r.2.1 ≤ Q.size (rep.ty (.pair scalar (.pair (.list scalar) (.list scalar)))) r.2 :=
    sizes.fst_le _ _ r.2
  have hr22 : Q.size (rep.ty (.pair (.list scalar) (.list scalar))) r.2.2 ≤
      Q.size (rep.ty (.pair scalar (.pair (.list scalar) (.list scalar)))) r.2 := sizes.snd_le _ _ r.2
  have hγ : Q.size (rep.ty (.list scalar)) r.2.2.1 ≤ Q.size (rep.ty (.pair (.list scalar) (.list scalar))) r.2.2 :=
    sizes.fst_le _ _ r.2.2
  have hξ : Q.size (rep.ty (.list scalar)) r.2.2.2 ≤ Q.size (rep.ty (.pair (.list scalar) (.list scalar))) r.2.2 :=
    sizes.snd_le _ _ r.2.2
  have hγc : r.2.2.1.length ≤ Q.size (rep.ty (.list scalar)) r.2.2.1 := lens.length_le_size _ _
  have hξc : r.2.2.2.length ≤ Q.size (rep.ty (.list scalar)) r.2.2.2 := lens.length_le_size _ _
  have hmk := marks_size rep sizes lists width cap hh hb hf marks hmarks
  have hmkr := marks_size rep sizes lists width cap hh hb hf marks.reverse (by rw [List.length_reverse]; exact hmarks)
  change Q.size (rep.ty (.list markTy)) marks ≤ _ at hmk
  change Q.size (rep.ty (.list markTy)) marks.reverse ≤ _ at hmkr
  have e0 := env_cons_size rep sizes lists mono (a := OutTy) (Γ := [.list markTy, scalar]) r (marks, v, ())
  have e1 := env_cons_size rep sizes lists mono (a := .list markTy) (Γ := [scalar]) marks (v, ())
  have e2 := env_cons_size rep sizes lists mono (a := scalar) (Γ := []) v ()
  have e3 : Q.size (rep.env []) () ≤ width := hu
  have hv := hf v
  change Q.size (rep.env finishEnv) (r, marks, v, ()) ≤ _ at e0
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, hmk, hmkr, by omega⟩

/-- The coefficient list of the finished output. -/
theorem coeffsExpr_time (lens : ListLengthLaws Q rep.data) (r : OutTy.Value (cryptoBase F G₁ G₂ K M))
    (marks : List (Mark F)) (v : F) (hr : Q.size (rep.ty OutTy) r ≤ outputWidth) (hmarks : marks.length ≤ cap) :
    (bound coeffsExpr).time (r, marks, v, ()) ≤
      coeffsTime overhead (frame width cap outputWidth) cap outputWidth opTime := by
  obtain ⟨hr1, hr21, hγ, hξ, hγc, hξc, hmk, hmkr, hE0⟩ :=
    finish_facts rep cost primitive primitiveBound sizes lists mono caps lens r marks v hr hmarks
  have hremap := remapExpr_time (Γ := finishEnv) (outputWidth := outputWidth) rep data cost primitive laws dataLaws
    primitiveBound sizes lists mono caps marks.reverse r.2.2.1 r.2.2.2 (r, marks, v, ())
  obtain ⟨hh, hu, hb, hn, hf, hEq, hSub, hAdd, hZero, hMul, hNeg⟩ := caps
  have hW := frame_eq width cap outputWidth
  have hmw := marksWidth_eq width cap
  have h25 : (2 * cap + 5) * width = 2 * (cap * width) + 5 * width := by ring
  have h21 : (2 * cap + 1) * width = 2 * (cap * width) + width := by ring
  have h2o : (2 * outputWidth + 1) * width = 2 * (outputWidth * width) + width := by ring
  generalize hWdef : frame width cap outputWidth = W at *
  have hw : width ≤ W := by omega
  have hhW : header ≤ W := by omega
  have hmark : ∀ x : Mark F, Q.size (rep.ty markTy) x ≤ 3 * width := mark_size rep sizes lists width hh hb hf
  have hlist : ∀ ys : List F, ys.length ≤ outputWidth → Q.size (rep.ty (.list scalar)) ys ≤ W := fun ys hys =>
    (scalars_size rep sizes lists width outputWidth hh hf ys hys).trans (by omega)
  have hr0 : Q.size (rep.ty OutTy) r ≤ W := by omega
  have hr2 : Q.size (rep.ty (.pair scalar (.pair (.list scalar) (.list scalar)))) r.2 ≤ Q.size (rep.ty OutTy) r :=
    sizes.snd_le _ _ r
  have hr22 : Q.size (rep.ty (.pair (.list scalar) (.list scalar))) r.2.2 ≤
      Q.size (rep.ty (.pair scalar (.pair (.list scalar) (.list scalar)))) r.2 := sizes.snd_le _ _ r.2
  have e1 := env_cons_size rep sizes lists mono (a := .list scalar) (Γ := finishEnv) r.2.2.2 (r, marks, v, ())
  have e2 := env_cons_size rep sizes lists mono (a := .list scalar) (Γ := .list scalar :: finishEnv) r.2.2.1
    (r.2.2.2, r, marks, v, ())
  have e3 := env_cons_size rep sizes lists mono (a := .list markTy) (Γ := .list scalar :: .list scalar :: finishEnv)
    marks.reverse (r.2.2.1, r.2.2.2, r, marks, v, ())
  have hE0' : Q.size (rep.env finishEnv) (r, marks, v, ()) ≤ W := by omega
  have hE1' : Q.size (rep.env (.list scalar :: finishEnv)) (r.2.2.2, r, marks, v, ()) ≤ W := by omega
  have hE2' : Q.size (rep.env (.list scalar :: .list scalar :: finishEnv)) (r.2.2.1, r.2.2.2, r, marks, v, ()) ≤ W := by
    omega
  have hE3 : Q.size (rep.env (remapEnv finishEnv)) (marks.reverse, r.2.2.1, r.2.2.2, r, marks, v, ()) +
      marksWidth width cap + (2 * cap + 5) * width + outputWidth + 16 * width ≤ W := by
    change Q.size (rep.env (remapEnv finishEnv)) _ ≤ _ at e3
    omega
  have tremap := hremap W hw (by rw [List.length_reverse]; exact hmarks) hE3 hγ hξ hγc hξc hlist
  have hcoeffsW : Q.size (rep.ty (.list scalar)) (coeffsExpr.denote arith (r, marks, v, ())) ≤ W := by
    rw [coeffsExpr_denote]
    exact (scalars_size rep sizes lists width cap hh hf _ (by simpa [remapMarks_length] using hmarks)).trans
      (by omega)
  dsimp only [coeffsExpr]
  have tv0 := var_depth_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Var.here : Var finishEnv OutTy) _ W 0 hE0' rfl
  have ts0 := SND _ _ W _ hE0' (by exact hr0) tv0
  have tss0 := SND _ _ W _ hE0' (by exact hr2.trans hr0) ts0
  have te1 := SND _ _ W _ hE0' (by exact (hr22.trans hr2).trans hr0) tss0
  have tv1 := var_depth_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Var.there .here : Var (.list scalar :: finishEnv) OutTy) _ W 1 hE1' rfl
  have ts1 := SND _ _ W _ hE1' (by exact hr0) tv1
  have tss1 := SND _ _ W _ hE1' (by exact hr2.trans hr0) ts1
  have te2 := FST _ _ W _ hE1' (by exact (hr22.trans hr2).trans hr0) tss1
  have tv3 := var_depth_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Var.there (.there (.there .here)) : Var (.list scalar :: .list scalar :: finishEnv) (.list markTy)) _ W 3 hE2' rfl
  have trev := ReverseCompiler.reverse_time_bound rep data arith primitive laws dataLaws primitiveBound sizes lists mono
    (cell := markTy) (Γ := .list scalar :: .list scalar :: finishEnv) marks (r.2.2.1, r.2.2.2, r, marks, v, ()) W cap
    hhW (hu.trans hw) hE2' (fun x _ => (hmark x).trans (by omega)) hmarks
  have te3 := LETE _ _ _ W _ _ hhW hE2' (by exact hmk.trans (by omega))
    (by rw [reverseList_denote]; exact hmkr.trans (by omega)) tv3 (by exact trev)
  have hrev : (Expr.letE (.var (Var.there (.there (.there .here)))) reverseList :
      Expr CryptoOp (.list scalar :: .list scalar :: finishEnv) (.list markTy)).denote arith
      (r.2.2.1, r.2.2.2, r, marks, v, ()) = marks.reverse := by
    change (reverseList (Op := CryptoOp) (cell := markTy) (Γ := .list scalar :: .list scalar :: finishEnv)).denote arith
      (marks, r.2.2.1, r.2.2.2, r, marks, v, ()) = _
    rw [reverseList_denote]
  have L3 := LETE _ _ _ W _ _ hhW hE2' (by rw [hrev]; exact hmkr.trans (by omega))
    (by
      change Q.size (rep.ty (.list scalar)) (coeffsExpr.denote arith (r, marks, v, ())) ≤ W
      exact hcoeffsW)
    te3 (by rewrite [hrev]; exact tremap)
  have L2 := LETE _ _ _ W _ _ hhW hE1' (by show Q.size (rep.ty (.list scalar)) r.2.2.1 ≤ W; omega)
    (by
      change Q.size (rep.ty (.list scalar)) (coeffsExpr.denote arith (r, marks, v, ())) ≤ W
      exact hcoeffsW)
    te2 L3
  have L1 := LETE _ _ _ W _ _ hhW hE0' (by show Q.size (rep.ty (.list scalar)) r.2.2.2 ≤ W; omega)
    (by
      change Q.size (rep.ty (.list scalar)) (coeffsExpr.denote arith (r, marks, v, ())) ≤ W
      exact hcoeffsW)
    te1 L2
  dsimp only [coeffsTime, reverseTime] at *
  linarith

/-- Appending the negated final scalar to a coefficient list of length at most `cap`. -/
theorem appendOne_time (lens : ListLengthLaws Q rep.data) (coeffs : List F) (r : OutTy.Value (cryptoBase F G₁ G₂ K M))
    (marks : List (Mark F)) (v : F) (hr : Q.size (rep.ty OutTy) r ≤ outputWidth) (hmarks : marks.length ≤ cap)
    (hc : coeffs.length ≤ cap) :
    (bound appendOne).time (coeffs, r, marks, v, ()) ≤ appendTime overhead (frame width cap outputWidth) cap opTime := by
  obtain ⟨hr1, hr21, hγ, hξ, hγc, hξc, hmk, hmkr, hE0⟩ :=
    finish_facts rep cost primitive primitiveBound sizes lists mono caps lens r marks v hr hmarks
  obtain ⟨hh, hu, hb, hn, hf, hEq, hSub, hAdd, hZero, hMul, hNeg⟩ := caps
  have hW := frame_eq width cap outputWidth
  have hmw := marksWidth_eq width cap
  have h23 : (2 * cap + 3) * width = 2 * (cap * width) + 3 * width := by ring
  generalize hWdef : frame width cap outputWidth = W at *
  have hw : width ≤ W := by omega
  have hhW : header ≤ W := by omega
  have hcap3 : (2 * cap + 3) * width ≤ W := by omega
  have hscal : ∀ ys : List F, ys.length ≤ cap + 1 → Q.size (rep.ty (.list scalar)) ys ≤ (2 * cap + 3) * width :=
    fun ys hys => scalars_size rep sizes lists width (cap + 1) hh hf ys hys
  have hcs := hscal coeffs (by omega)
  have hcsr := hscal coeffs.reverse (by rw [List.length_reverse]; omega)
  have e0 := env_cons_size rep sizes lists mono (a := .list scalar) (Γ := finishEnv) coeffs (r, marks, v, ())
  have hE' : Q.size (rep.env (.list scalar :: finishEnv)) (coeffs, r, marks, v, ()) ≤ W := by omega
  have hbodyEnv : ∀ (x : F) (acc : List F), acc.length ≤ cap + 1 →
      Q.size (rep.env (scalar :: .list scalar :: .list scalar :: finishEnv)) (x, acc, coeffs, r, marks, v, ()) ≤ W := by
    intro x acc hacc
    have e1 := env_cons_size rep sizes lists mono (a := .list scalar) (Γ := .list scalar :: finishEnv) acc
      (coeffs, r, marks, v, ())
    have e2 := env_cons_size rep sizes lists mono (a := scalar) (Γ := .list scalar :: .list scalar :: finishEnv) x
      (acc, coeffs, r, marks, v, ())
    have := hscal acc hacc
    have := hf x
    omega
  have hxsval : (Expr.letE (.var Var.here) reverseList :
      Expr CryptoOp (.list scalar :: finishEnv) (.list scalar)).denote arith (coeffs, r, marks, v, ()) = coeffs.reverse := by
    change (reverseList (Op := CryptoOp) (cell := scalar) (Γ := .list scalar :: finishEnv)).denote arith
      (coeffs, coeffs, r, marks, v, ()) = _
    rw [reverseList_denote]
  dsimp only [appendOne]
  have tv0 := var_depth_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Var.here : Var (.list scalar :: finishEnv) (.list scalar)) _ W 0 hE' rfl
  have trev := ReverseCompiler.reverse_time_bound rep data arith primitive laws dataLaws primitiveBound sizes lists mono
    (cell := scalar) (Γ := .list scalar :: finishEnv) coeffs (coeffs, r, marks, v, ()) W cap
    hhW (hu.trans hw) hE' (fun x _ => (hf x).trans hw) hc
  have txs := LETE _ _ _ W _ _ hhW hE' (by exact hcs.trans hcap3)
    (by rw [reverseList_denote]; exact hcsr.trans hcap3) tv0 (by exact trev)
  have tv3 := var_depth_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Var.there (.there (.there .here)) : Var (.list scalar :: finishEnv) scalar) _ W 3 hE' rfl
  have tneg := OPT CryptoOp.neg _ _ W _ _ hE' (by exact (hf _).trans hw) (by exact (hf _).trans hw) tv3 (by exact hNeg _)
  have tnil : (bound (.nil : Expr CryptoOp (.list scalar :: finishEnv) (.list scalar))).time (coeffs, r, marks, v, ()) ≤
      3 * frameFee overhead W := NIL _ W hhW hE' (hu.trans hw)
  have tinit := CONS _ _ _ W _ _ hhW hE' (by exact (hf _).trans hw) (by exact (lists.nil_le _).trans hhW) tneg tnil
  have twork := foldWork_bound_remaining
    (fun (x : F) (acc : List F) =>
      (Expr.cons (.var .here) (.var (.there .here)) :
        Expr CryptoOp (scalar :: .list scalar :: .list scalar :: finishEnv) (.list scalar)).denote arith (x, acc, coeffs, r, marks, v, ()))
    (fun (x : F) (acc : List F) => (bound (Expr.cons (.var .here) (.var (.there .here)) :
      Expr CryptoOp (scalar :: .list scalar :: .list scalar :: finishEnv) (.list scalar))).time
        (x, acc, coeffs, r, marks, v, ()))
    (foldFee (Q := Q) overhead rep.data (rep.ty scalar) (rep.ty (.list scalar)) (rep.env (.list scalar :: finishEnv))
      ((Expr.cons (.var .here) (.var (.there .here)) :
        Expr CryptoOp (scalar :: .list scalar :: .list scalar :: finishEnv) (.list scalar)).denote arith) (coeffs, r, marks, v, ()))
    (fun _ => True) (fun remaining (acc : List F) => acc.length + remaining ≤ cap + 1)
    (7 * frameFee overhead W) (frameFee overhead W) cap
    (by
      intro remaining hrem x _ (acc : List F) hinv
      try dsimp only at hinv
      have henv := hbodyEnv x acc (by omega)
      have tx := var_depth_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        (Var.here : Var (scalar :: .list scalar :: .list scalar :: finishEnv) scalar) _ W 0 henv rfl
      have ta := var_depth_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        (Var.there .here : Var (scalar :: .list scalar :: .list scalar :: finishEnv) (.list scalar)) _ W 1 henv rfl
      have tc := CONS _ _ _ W _ _ hhW henv (by exact (hf x).trans hw) (by exact (hscal acc (by omega)).trans hcap3) tx ta
      refine ⟨tc.trans (by omega), ?_⟩
      show (x :: acc).length + remaining ≤ cap + 1
      simp only [List.length_cons]
      omega)
    (by
      intro xs hxs _ (acc : List F) hinv
      try dsimp only at hinv
      unfold foldFee
      apply mono
      have e1 := env_cons_size rep sizes lists mono (a := .list scalar) (Γ := .list scalar :: finishEnv) acc
        (coeffs, r, marks, v, ())
      have e2 := env_cons_size rep sizes lists mono (a := .list scalar) (Γ := .list scalar :: .list scalar :: finishEnv) xs
        (acc, coeffs, r, marks, v, ())
      have hxsS := hscal xs (by omega)
      have haccS := hscal acc (by omega)
      change Q.size (rep.env (.list scalar :: .list scalar :: .list scalar :: finishEnv)) (xs, acc, coeffs, r, marks, v, ()) +
        Q.size (rep.ty (.list scalar)) (xs.foldl (fun acc x => x :: acc) acc) ≤ 16 * W
      rw [foldl_cons_eq]
      have hresS := hscal (xs.reverse ++ acc) (by simp only [List.length_append, List.length_reverse]; omega)
      omega)
    coeffs.reverse (by rw [List.length_reverse]; exact hc) (fun _ _ => trivial) [-v] (by simp; omega)
  have tf := FOLD _ _ _ _ W _ _ (cap * (7 * frameFee overhead W + frameFee overhead W) + frameFee overhead W) hhW hE'
    (by rw [hxsval]; exact hcsr.trans hcap3)
    (by
      show Q.size (rep.ty (.list scalar)) [_] ≤ W
      exact (hscal _ (by simp)).trans hcap3)
    (by
      change Q.size (rep.ty (.list scalar)) (appendOne.denote arith (coeffs, r, marks, v, ())) ≤ W
      rw [appendOne_denote]
      exact (hscal _ (by simp only [List.length_append, List.length_singleton]; omega)).trans hcap3)
    txs tinit
    (by
      rewrite [hxsval]
      exact twork.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by rw [List.length_reverse]; exact hc)) _))
  dsimp only [appendTime, reverseTime] at *
  linarith

/-- The complete finish. -/
theorem finExpr_time (lens : ListLengthLaws Q rep.data) (r : OutTy.Value (cryptoBase F G₁ G₂ K M))
    (marks : List (Mark F)) (v : F) (hr : Q.size (rep.ty OutTy) r ≤ outputWidth) (hmarks : marks.length ≤ cap) :
    (bound finExpr).time (r, marks, v, ()) ≤ finishTime overhead width cap outputWidth opTime := by
  have tcoeffs := coeffsExpr_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono caps lens
    r marks v hr hmarks
  have tapp := appendOne_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono caps lens
    (coeffsExpr.denote arith (r, marks, v, ())) r marks v hr hmarks
    (by rw [coeffsExpr_denote, remapMarks_length, List.length_reverse]; exact hmarks)
  obtain ⟨hr1, hr21, hγ, hξ, hγc, hξc, hmk, hmkr, hE0⟩ :=
    finish_facts rep cost primitive primitiveBound sizes lists mono caps lens r marks v hr hmarks
  obtain ⟨hh, hu, hb, hn, hf, hEq, hSub, hAdd, hZero, hMul, hNeg⟩ := caps
  have hW := frame_eq width cap outputWidth
  have hmw := marksWidth_eq width cap
  have h23 : (2 * cap + 3) * width = 2 * (cap * width) + 3 * width := by ring
  dsimp only [finishTime] at *
  generalize hWdef : frame width cap outputWidth = W at *
  have hw : width ≤ W := by omega
  have hhW : header ≤ W := by omega
  have hcap3 : (2 * cap + 3) * width ≤ W := by omega
  have hscal : ∀ ys : List F, ys.length ≤ cap + 1 → Q.size (rep.ty (.list scalar)) ys ≤ (2 * cap + 3) * width :=
    fun ys hys => scalars_size rep sizes lists width (cap + 1) hh hf ys hys
  have hclen : (coeffsExpr.denote arith (r, marks, v, ())).length ≤ cap := by
    rw [coeffsExpr_denote, remapMarks_length, List.length_reverse]; exact hmarks
  have hcs := hscal _ (hclen.trans (Nat.le_succ cap))
  have hfinal : (appendOne.denote arith (coeffsExpr.denote arith (r, marks, v, ()), r, marks, v, ())).length ≤ cap + 1 := by
    rw [appendOne_denote]; simp only [List.length_append, List.length_singleton]; omega
  have hfs := hscal _ hfinal
  have hr0 : Q.size (rep.ty OutTy) r ≤ W := by omega
  have hr2 : Q.size (rep.ty (.pair scalar (.pair (.list scalar) (.list scalar)))) r.2 ≤ Q.size (rep.ty OutTy) r :=
    sizes.snd_le _ _ r
  have hr22 : Q.size (rep.ty (.pair (.list scalar) (.list scalar))) r.2.2 ≤
      Q.size (rep.ty (.pair scalar (.pair (.list scalar) (.list scalar)))) r.2 := sizes.snd_le _ _ r.2
  have e0 := env_cons_size rep sizes lists mono (a := .list scalar) (Γ := finishEnv)
    (coeffsExpr.denote arith (r, marks, v, ())) (r, marks, v, ())
  have hE' : Q.size (rep.env (.list scalar :: finishEnv)) (coeffsExpr.denote arith (r, marks, v, ()), r, marks, v, ()) ≤ W := by
    omega
  have hE0' : Q.size (rep.env finishEnv) (r, marks, v, ()) ≤ W := by omega
  have pA := sizes.prod_le (rep.ty (.list scalar)) (rep.ty (.list scalar))
    (appendOne.denote arith (coeffsExpr.denote arith (r, marks, v, ()), r, marks, v, ()), r.2.2.2)
  have pB := sizes.prod_le (rep.ty scalar) (rep.ty (.pair (.list scalar) (.list scalar)))
    (r.2.1, appendOne.denote arith (coeffsExpr.denote arith (r, marks, v, ()), r, marks, v, ()), r.2.2.2)
  have pC := sizes.prod_le (rep.ty Weights.syncMessage) (rep.ty (.pair scalar (.pair (.list scalar) (.list scalar))))
    (r.1, r.2.1, appendOne.denote arith (coeffsExpr.denote arith (r, marks, v, ()), r, marks, v, ()), r.2.2.2)
  dsimp only at pA pB pC
  change Q.size (rep.ty (.pair (.list scalar) (.list scalar))) _ ≤ _ at pA
  change Q.size (rep.ty (.pair scalar (.pair (.list scalar) (.list scalar)))) _ ≤ _ at pB
  change Q.size (rep.ty OutTy) _ ≤ _ at pC
  dsimp only [finExpr]
  have tv1 := var_depth_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Var.there .here : Var (.list scalar :: finishEnv) OutTy) _ W 1 hE' rfl
  have tf1 := FST _ _ W _ hE' (by exact hr0) tv1
  have ts1 := SND _ _ W _ hE' (by exact hr0) tv1
  have tfs1 := FST _ _ W _ hE' (by exact hr2.trans hr0) ts1
  have tss1 := SND _ _ W _ hE' (by exact hr2.trans hr0) ts1
  have tsss1 := SND _ _ W _ hE' (by exact (hr22.trans hr2).trans hr0) tss1
  have pa := PAIR _ _ _ W _ _ hhW hE' (by exact hfs.trans hcap3)
    (by show Q.size (rep.ty (.list scalar)) r.2.2.2 ≤ W; omega) tapp tsss1
  have pb := PAIR _ _ _ W _ _ hhW hE' (by show Q.size (rep.ty scalar) r.2.1 ≤ W; omega)
    (by
      show Q.size (rep.ty (.pair (.list scalar) (.list scalar))) (_, r.2.2.2) ≤ W
      omega)
    tfs1 pa
  have pc := PAIR _ _ _ W _ _ hhW hE' (by show Q.size (rep.ty Weights.syncMessage) r.1 ≤ W; omega)
    (by
      show Q.size (rep.ty (.pair scalar (.pair (.list scalar) (.list scalar)))) (r.2.1, _, r.2.2.2) ≤ W
      omega)
    tf1 pb
  have L := LETE _ _ _ W _ _ hhW hE0' (by exact hcs.trans hcap3)
    (by
      change Q.size (rep.ty OutTy) (finExpr.denote arith (r, marks, v, ())) ≤ W
      show Q.size (rep.ty OutTy) (r.1, r.2.1, _, r.2.2.2) ≤ W
      omega)
    tcoeffs pc
  linarith

include laws dataLaws in
/-- The compiled finish runs within `finishTime`. -/
theorem finish_cost (lens : ListLengthLaws Q rep.data) (r : OutTy.Value (cryptoBase F G₁ G₂ K M))
    (marks : List (Mark F)) (v : F) (hr : Q.size (rep.ty OutTy) r ≤ outputWidth) (hmarks : marks.length ≤ cap) :
    Q.cost (Expression.compile rep data arith primitive finExpr) (r, marks, v, ()) ≤
      finishTime overhead width cap outputWidth opTime :=
  (Expression.cost_compile_le rep data arith primitive laws dataLaws primitiveBound finExpr _).trans
    (finExpr_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono caps lens r marks v hr hmarks)

end Signatures.Runtime.SyncWrapGeneral
