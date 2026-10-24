import Proofs.Runtime.BackendExpressionCost
import Proofs.Runtime.BackendDataSize
import Proofs.Runtime.LookupExpr

/-! Native list lookup with an actual comparison expression. The comparator
runs in its retained environment; its cost premise includes that environment.
The Schnorr specialization derives this premise from message/point primitives. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram.LookupExprCompiler

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  (P : Primitives base Op)
  (primitive : {a b : Ty Atom} → (instr : Op a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))
  {overhead : Nat → Nat} (localLaws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty Atom} → (instr : Op a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (mono : Monotone overhead)

include sizes mono

theorem body_time_bound {key val : Ty Atom} (eq : Expr Op [key, key] .bool)
    (p : key.Value base × val.Value base) (acc : Bool × val.Value base)
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base))
    (width comparisonTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hp : Q.size (rep.ty key) p.1 ≤ width) (hv : Q.size (rep.ty val) p.2 ≤ width)
    (ha : Q.size (rep.ty val) acc.2 ≤ width) (hk : Q.size (rep.ty key) k ≤ width)
    (hd : Q.size (rep.ty val) default ≤ width)
    (hl : Q.size (rep.ty (.list (.pair key val))) xs ≤ width)
    (he : (Expression.compileBound rep data P primitive localLaws dataLaws primitiveBound
      (eq.weakenTail [.pair key val, .pair .bool val, key, val, .list (.pair key val)])).time
        (p.1, k, p, acc, k, default, xs, ()) ≤ comparisonTime) :
    (Expression.compileBound rep data P primitive localLaws dataLaws primitiveBound (lookupExprBody eq)).time
      (p, acc, k, default, xs, ()) ≤ comparisonTime + 512 * overhead (128 * width) := by
  have hfee : ∀ n, n ≤ 128 * width → overhead n ≤ overhead (128 * width) := fun n hn => mono hn
  have hprod : ∀ {A B : Type} (a : C.Str A) (b : C.Str B) (input : A × B),
      Q.size (StepClass.HasProd.prod a b) input ≤ Q.size a input.1 + Q.size b input.2 + header :=
    fun a b input => sizes.prod_le a b input
  have hsum : ∀ {A B : Type} (a : C.Str A) (b : C.Str B) (input : A ⊕ B),
      Q.size (StepClass.HasSum.sum a b) input ≤ Sum.elim (Q.size a) (Q.size b) input + header :=
    fun a b input => sizes.sum_le a b input
  have hentry := sizes.prod_le (rep.ty key) (rep.ty val) p
  have hacc := sizes.prod_le rep.data.bool (rep.ty val) acc
  have htail := sizes.prod_le (rep.ty (.list (.pair key val))) rep.data.unit (xs, ())
  have hdefault := sizes.prod_le (rep.ty val) (rep.env [.list (.pair key val)]) (default, xs, ())
  have hkey := sizes.prod_le (rep.ty key) (rep.env [val, .list (.pair key val)]) (k, default, xs, ())
  have haccEnv := sizes.prod_le (rep.ty (.pair .bool val)) (rep.env [key, val, .list (.pair key val)])
    (acc, k, default, xs, ())
  have hroot := sizes.prod_le (rep.ty (.pair key val))
    (rep.env [.pair .bool val, key, val, .list (.pair key val)]) (p, acc, k, default, xs, ())
  have hselected (b : Bool) := sizes.prod_le rep.data.bool
    (rep.env [.pair key val, .pair .bool val, key, val, .list (.pair key val)]) (b, p, acc, k, default, xs, ())
  have hleft := sizes.sum_le
    (rep.env [.pair key val, .pair .bool val, key, val, .list (.pair key val)])
    (rep.env [.pair key val, .pair .bool val, key, val, .list (.pair key val)])
      (.inl (p, acc, k, default, xs, ()))
  have hright := sizes.sum_le
    (rep.env [.pair key val, .pair .bool val, key, val, .list (.pair key val)])
    (rep.env [.pair key val, .pair .bool val, key, val, .list (.pair key val)])
      (.inr (p, acc, k, default, xs, ()))
  have hcompare := sizes.prod_le (rep.ty key) (rep.ty key) (p.1, k)
  have hanswer := sizes.prod_le rep.data.bool (rep.ty val) (true, p.2)
  dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env, Sum.elim] at *
  by_cases hfound : acc.1 = true <;>
    dsimp only [lookupExprBody, Expression.compileBound, Expression.variableBound,
      LocalBound.castFunction, LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
      LocalBound.identity, LocalBound.elim, DataCostLaws.unitBound, DataCostLaws.boolBound,
      DataCostLaws.selectBound, Expr.denote, Var.get,
      LanguageRepresentation.ty, LanguageRepresentation.env] <;>
    dsimp only [id, Function.comp_def, Sum.elim] <;>
    simp only [hfound] <;>
    generalize hcost : (Expression.compileBound rep data P primitive localLaws dataLaws primitiveBound
      (eq.weakenTail [.pair key val, .pair .bool val, key, val, .list (.pair key val)])).time
        (p.1, k, p, acc, k, default, xs, ()) = actualCost at * <;>
    generalize hvalue : (eq.weakenTail [.pair key val, .pair .bool val, key, val, .list (.pair key val)]).denote P
      (p.1, k, p, acc, k, default, xs, ()) = compared at * <;>
    cases compared <;>
    simp only [hcost, hvalue, Bool.false_eq_true, ite_false, ite_true] at * <;>
    grind only

theorem lookup_time_bound_of_caps {key val : Ty Atom} (eq : Expr Op [key, key] .bool)
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base))
    (width comparisonTime cap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hk : Q.size (rep.ty key) k ≤ width) (hd : Q.size (rep.ty val) default ≤ width)
    (hv : ∀ p ∈ xs, Q.size (rep.ty key) p.1 ≤ width ∧ Q.size (rep.ty val) p.2 ≤ width)
    (hn : xs.length ≤ cap)
    (hl : ∀ ys : List (key.Value base × val.Value base), ys.length ≤ cap →
      (∀ p ∈ ys, p ∈ xs) → Q.size (rep.ty (.list (.pair key val))) ys ≤ width)
    (he : ∀ p ∈ xs, ∀ acc : Bool × val.Value base, Q.size (rep.ty val) acc.2 ≤ width →
      (Expression.compileBound rep data P primitive localLaws dataLaws primitiveBound
        (eq.weakenTail [.pair key val, .pair .bool val, key, val, .list (.pair key val)])).time
          (p.1, k, p, acc, k, default, xs, ()) ≤ comparisonTime) :
    (Expression.compileBound rep data P primitive localLaws dataLaws primitiveBound (lookupExpr eq)).time
      (k, default, xs, ()) ≤ cap * (comparisonTime + 513 * overhead (128 * width)) +
        32 * overhead (128 * width) := by
  let step := fun (p : key.Value base × val.Value base) (acc : Bool × val.Value base) =>
    (lookupExprBody eq).denote P (p, acc, k, default, xs, ())
  have hstep (p : key.Value base × val.Value base) (hp : p ∈ xs)
      (acc : Bool × val.Value base) (ha : Q.size (rep.ty val) acc.2 ≤ width) :
      Q.size (rep.ty val) (step p acc).2 ≤ width := by
    have hweak := eq.weakenTail_denote
      (Δ := [.pair key val, .pair .bool val, key, val, .list (.pair key val)])
      P (p.1, k, ()) (p, acc, k, default, xs, ())
    simp only [Env.append] at hweak
    simp only [step, lookupExprBody, Expr.denote, Var.get, hweak]
    change Q.size (rep.ty val)
      (if acc.1 = true then acc else if eq.denote P (p.1, k, ()) = true then (true, p.2) else acc).2 ≤ width
    by_cases hfound : acc.1 = true <;> by_cases heq : eq.denote P (p.1, k, ()) = true <;>
      simp only [hfound, heq, ite_true] <;> first | exact ha | exact (hv p hp).2
  have hfold (ys : List (key.Value base × val.Value base)) (hy : ∀ p ∈ ys, p ∈ xs)
      (acc : Bool × val.Value base) (ha : Q.size (rep.ty val) acc.2 ≤ width) :
      Q.size (rep.ty val) (ys.foldl (fun acc p => step p acc) acc).2 ≤ width := by
    induction ys generalizing acc with
    | nil => exact ha
    | cons p ys ih =>
        exact ih (fun q hq => hy q (by simp [hq])) (step p acc) (hstep p (hy p (by simp)) acc ha)
  have hxs := hl xs hn (fun _ h => h)
  have htail := sizes.prod_le (rep.ty (.list (.pair key val))) rep.data.unit (xs, ())
  have hdefault := sizes.prod_le (rep.ty val) (rep.env [.list (.pair key val)]) (default, xs, ())
  have henv := sizes.prod_le (rep.ty key) (rep.env [val, .list (.pair key val)]) (k, default, xs, ())
  have hwork := foldWork_bound step
    (fun p acc => (Expression.compileBound rep data P primitive localLaws dataLaws primitiveBound (lookupExprBody eq)).time
      (p, acc, k, default, xs, ()))
    (foldFee (Q := Q) overhead rep.data (rep.ty (.pair key val)) (rep.ty (.pair .bool val))
      (rep.env [key, val, .list (.pair key val)]) ((lookupExprBody eq).denote P) (k, default, xs, ()))
    (fun p => p ∈ xs) (fun acc => Q.size (rep.ty val) acc.2 ≤ width)
    (comparisonTime + 512 * overhead (128 * width)) (overhead (128 * width)) cap
    (by
      intro p hp acc ha
      exact ⟨body_time_bound rep data P primitive localLaws dataLaws primitiveBound sizes mono eq
        p acc k default xs width comparisonTime hh hu hb (hv p hp).1 (hv p hp).2 ha hk hd hxs (he p hp acc ha),
        hstep p hp acc ha⟩)
    (by
      intro ys hlen hys acc ha
      have hysSize := hl ys hlen hys
      have hout := hfold ys hys acc ha
      have hac := sizes.prod_le rep.data.bool (rep.ty val) acc
      have hacc := sizes.prod_le (rep.ty (.pair .bool val))
        (rep.env [key, val, .list (.pair key val)]) (acc, k, default, xs, ())
      have hin := sizes.prod_le (rep.ty (.list (.pair key val)))
        (StepClass.HasProd.prod (rep.ty (.pair .bool val)) (rep.env [key, val, .list (.pair key val)]))
          (ys, acc, k, default, xs, ())
      have hresult := sizes.prod_le rep.data.bool (rep.ty val) (ys.foldl (fun acc p => step p acc) acc)
      have hba := hb acc.1
      have hbo := hb (ys.foldl (fun acc p => step p acc) acc).1
      unfold foldFee
      apply mono
      dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env, step] at *
      grind only)
    xs hn (fun _ h => h) (false, default) hd
  have hf : Q.size (rep.ty val) (xs.foldl (fun acc p => step p acc) (false, default)).2 ≤ width :=
    hfold xs (fun _ h => h) (false, default) hd
  have hinit := sizes.prod_le rep.data.bool (rep.ty val) (false, default)
  have hacc := sizes.prod_le (rep.ty (.pair .bool val))
    (rep.env [key, val, .list (.pair key val)]) ((false, default), k, default, xs, ())
  have hin := sizes.prod_le (rep.ty (.list (.pair key val)))
    (StepClass.HasProd.prod (rep.ty (.pair .bool val)) (rep.env [key, val, .list (.pair key val)]))
      (xs, (false, default), k, default, xs, ())
  have hout := sizes.prod_le rep.data.bool (rep.ty val) (xs.foldl (fun acc p => step p acc) (false, default))
  have hbf := hb false
  have hbo := hb (xs.foldl (fun acc p => step p acc) (false, default)).1
  have hcap := Nat.mul_le_mul_right
    (comparisonTime + 512 * overhead (128 * width) + overhead (128 * width)) hn
  have hfee : ∀ n, n ≤ 128 * width → overhead n ≤ overhead (128 * width) := fun _ h => mono h
  dsimp only [lookupExpr, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.foldBound, DataCostLaws.unitBound, DataCostLaws.boolBound,
    Expr.denote, Var.get, LanguageRepresentation.ty, LanguageRepresentation.env, step, id] at *
  grind only

include localLaws dataLaws

/-- A list representation contract supplies the scan's frame-width obligation.
The bound counts stored entries and their encoded sizes, independently of the
size or finiteness of the key universe. The comparison premise covers the actual
weakened comparator on encountered keys and bounded retained contexts. -/
theorem lookup_cost_bound (lists : ListSizeLaws Q rep.data header)
    {key val : Ty Atom} (eq : Expr Op [key, key] .bool)
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base))
    (width comparisonTime cap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hk : Q.size (rep.ty key) k ≤ width) (hd : Q.size (rep.ty val) default ≤ width)
    (hv : ∀ p ∈ xs, Q.size (rep.ty key) p.1 ≤ width ∧ Q.size (rep.ty val) p.2 ≤ width)
    (hn : xs.length ≤ cap)
    (he : ∀ p ∈ xs, ∀ acc : Bool × val.Value base,
      Q.size (rep.ty val) acc.2 ≤ (4 * cap + 1) * width →
      (Expression.compileBound rep data P primitive localLaws dataLaws primitiveBound
        (eq.weakenTail [.pair key val, .pair .bool val, key, val, .list (.pair key val)])).time
          (p.1, k, p, acc, k, default, xs, ()) ≤ comparisonTime) :
    Q.cost (Expression.compile rep data P primitive (lookupExpr eq)) (k, default, xs, ()) ≤
      cap * (comparisonTime + 513 * overhead (128 * ((4 * cap + 1) * width))) +
        32 * overhead (128 * ((4 * cap + 1) * width)) := by
  have hw : width ≤ (4 * cap + 1) * width := by nlinarith
  apply (Expression.cost_compile_le rep data P primitive localLaws dataLaws primitiveBound (lookupExpr eq)
    (k, default, xs, ())).trans
  apply lookup_time_bound_of_caps rep data P primitive localLaws dataLaws primitiveBound sizes mono eq
    k default xs ((4 * cap + 1) * width) comparisonTime cap (hh.trans hw) (hu.trans hw)
    (fun b => (hb b).trans hw) (hk.trans hw) (hd.trans hw)
    (fun p hp => ⟨(hv p hp).1.trans hw, (hv p hp).2.trans hw⟩) hn ?_ he
  intro ys hlen hys
  have hlist := lists.size_le_cap (rep.ty (.pair key val)) ys (2 * width + header) cap (by
    intro p hp
    have hs := sizes.prod_le (rep.ty key) (rep.ty val) p
    obtain ⟨hkey, hval⟩ := hv p (hys p hp)
    exact hs.trans (by omega)) hlen
  have hm := Nat.mul_le_mul_left cap hh
  dsimp only [LanguageRepresentation.ty] at hlist ⊢
  nlinarith

end Signatures.Runtime.BackendProgram.LookupExprCompiler
