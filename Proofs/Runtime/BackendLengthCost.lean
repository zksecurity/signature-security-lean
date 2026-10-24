import Proofs.Runtime.BackendFoldGrowth
import Proofs.Runtime.BackendExpressionCost
import Proofs.Runtime.BackendExpressionSize
import Proofs.Runtime.BackendDataSize
import Proofs.Runtime.Length

/-! Native cost of computing the loop count from an actual list. Every
increment, retained frame, and fold-control operation is charged. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram.LengthCompiler

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  (P : Primitives base Op)
  (primitive : {a b : Ty Atom} → (instr : Op a b) → Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty Atom} → (instr : Op a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead)

include sizes mono

theorem body_time_bound {cell : Ty Atom} {Γ : List (Ty Atom)}
    (add : Op (.pair .nat .nat) .nat) (ha : ∀ x y, P.execute add (x, y) = x + y)
    (x : cell.Value base) (n : Nat) (env : Env base Γ) (width addTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env (cell :: .nat :: Γ)) (x, n, env) ≤ width)
    (h1 : Q.size rep.data.nat 1 ≤ width) (hn : Q.size rep.data.nat (n + 1) ≤ width)
    (ht : (primitiveBound add).time (n, 1) ≤ addTime) :
    (Expression.compileBound rep data P primitive laws dataLaws primitiveBound
      (.op add (.pair (.var (.there .here)) (.nat 1)) : Expr Op (cell :: .nat :: Γ) .nat)).time
        (x, n, env) ≤ addTime + 16 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  have hadd := ha n 1
  dsimp only [Expression.compileBound, Expression.variableBound, LocalBound.compose, LocalBound.pair,
    LocalBound.fst, LocalBound.snd, DataCostLaws.unitBound, DataCostLaws.natBound,
    Expr.denote, Var.get, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  rw [hadd]
  clear ha
  grind only

include lists in
theorem length_time_bound {cell : Ty Atom} {Γ : List (Ty Atom)}
    (add : Op (.pair .nat .nat) .nat) (ha : ∀ x y, P.execute add (x, y) = x + y)
    (xs : List (cell.Value base)) (env : Env base Γ) (width cap addTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width)
    (hx : ∀ x ∈ xs, Q.size (rep.ty cell) x ≤ width) (hc : xs.length ≤ cap)
    (hn : ∀ n ≤ cap + 1, Q.size rep.data.nat n ≤ width)
    (ht : ∀ n ≤ cap, (primitiveBound add).time (n, 1) ≤ addTime) :
    (Expression.compileBound rep data P primitive laws dataLaws primitiveBound
      (listLength (cell := cell) (Γ := Γ) add)).time (xs, env) ≤
        cap * (addTime + 17 * overhead (128 * ((4 * cap + 16) * width))) +
          32 * overhead (128 * ((4 * cap + 16) * width)) := by
  let W := (4 * cap + 16) * width
  let fee := overhead (128 * W)
  let inv := fun remaining n => n + remaining ≤ cap
  have hw : width ≤ W := by dsimp [W]; nlinarith
  have hprod := @sizes.prod_le
  have hlist (ys : List (cell.Value base)) (hlen : ys.length ≤ cap) (hy : ∀ y ∈ ys, y ∈ xs) :
      Q.size (rep.ty (.list cell)) ys ≤ (2 * cap + 1) * width := by
    have h := lists.size_le_cap (rep.ty cell) ys width cap (fun y hym => hx y (hy y hym)) hlen
    change Q.size (rep.ty (.list cell)) ys ≤ _ at h
    nlinarith [Nat.mul_le_mul_left cap hh]
  have hxs := hlist xs hc (fun _ h => h)
  have henv : Q.size (rep.env (.list cell :: Γ)) (xs, env) ≤ (2 * cap + 3) * width := by
    have h := sizes.prod_le (rep.ty (.list cell)) (rep.env Γ) (xs, env)
    change Q.size (rep.env (.list cell :: Γ)) (xs, env) ≤ _ at h
    dsimp only at h
    nlinarith
  have hwork := foldWork_bound_remaining (fun (_ : cell.Value base) n => n + 1)
    (fun x n => (Expression.compileBound rep data P primitive laws dataLaws primitiveBound
      (.op add (.pair (.var (.there .here)) (.nat 1)) : Expr Op (cell :: .nat :: .list cell :: Γ) .nat)).time
        (x, n, xs, env))
    (foldFee (Q := Q) overhead rep.data (rep.ty cell) rep.data.nat (rep.env (.list cell :: Γ))
      (fun p => p.2.1 + 1) (xs, env)) (fun x => x ∈ xs) inv (addTime + 16 * fee) fee cap
    (by
      intro remaining hr x hx' n hnv
      have hnSize := hn n (by dsimp [inv] at hnv; omega)
      have hxSize := hx x hx'
      have hi : Q.size (rep.env (cell :: .nat :: .list cell :: Γ)) (x, n, xs, env) ≤ W := by
        dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, W] at *
        clear hn ht ha
        grind only
      refine ⟨body_time_bound rep data P primitive laws dataLaws primitiveBound sizes mono
        (Γ := .list cell :: Γ) add ha
        x n (xs, env) W addTime (hh.trans hw) (hu.trans hw) hi
        ((hn 1 (by omega)).trans hw) ((hn (n + 1) (by dsimp [inv] at hnv; omega)).trans hw)
        (ht n (by dsimp [inv] at hnv; omega)), ?_⟩
      dsimp [inv] at *
      omega)
    (by
      intro ys hlen hys n hnv
      have hysSize := hlist ys hlen hys
      have hnSize := hn n (by dsimp [inv] at hnv; omega)
      have hoSize := hn (n + ys.length) (by dsimp [inv] at hnv; omega)
      unfold foldFee
      rw [fold_count]
      apply mono
      dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, W] at *
      clear hn ht ha
      grind only)
    xs hc (fun _ h => h) 0 (by simpa [inv])
  have hz := hn 0 (by omega)
  have hout := hn xs.length (by omega)
  have hfee : ∀ k ≤ 128 * W, overhead k ≤ fee := fun _ hk => mono hk
  have hcap := Nat.mul_le_mul_right (addTime + 17 * fee) hc
  dsimp only [listLength, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.foldBound, DataCostLaws.unitBound, DataCostLaws.natBound,
    Expr.denote, Var.get, LanguageRepresentation.env, LanguageRepresentation.ty, id] at *
  simp only [ha, fold_count, Nat.zero_add] at *
  clear hn ht ha
  dsimp only [fee, W] at *
  grind only

include laws dataLaws primitiveBound lists in
theorem length_cost_bound {cell : Ty Atom} {Γ : List (Ty Atom)}
    (add : Op (.pair .nat .nat) .nat) (ha : ∀ x y, P.execute add (x, y) = x + y)
    (xs : List (cell.Value base)) (env : Env base Γ) (width cap addTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width)
    (hx : ∀ x ∈ xs, Q.size (rep.ty cell) x ≤ width) (hc : xs.length ≤ cap)
    (hn : ∀ n ≤ cap + 1, Q.size rep.data.nat n ≤ width)
    (ht : ∀ n ≤ cap, (primitiveBound add).time (n, 1) ≤ addTime) :
    Q.cost (Expression.compile rep data P primitive (listLength (cell := cell) (Γ := Γ) add)) (xs, env) ≤
      cap * (addTime + 17 * overhead (128 * ((4 * cap + 16) * width))) +
        32 * overhead (128 * ((4 * cap + 16) * width)) :=
  (Expression.cost_compile_le rep data P primitive laws dataLaws primitiveBound _ _).trans
    (length_time_bound rep data P primitive laws dataLaws primitiveBound sizes lists mono
      add ha xs env width cap addTime hh hu he hx hc hn ht)

omit sizes mono [C.HasOption] in
theorem length_description {cell : Ty Atom} {Γ : List (Ty Atom)}
    (add : Op (.pair .nat .nat) .nat) (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    sizes.localSize (Expression.compile rep data P primitive (listLength (cell := cell) (Γ := Γ) add)) ≤
      sizes.localSize (primitive add) + 32 * allowance + 4 := by
  have h := Expression.compile_size rep data P primitive sizes allowance laws dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl) (listLength (cell := cell) (Γ := Γ) add)
  simp only [listLength, Expression.descriptionBound, Expression.variableDescription] at h
  exact h.trans (by omega)

end Signatures.Runtime.BackendProgram.LengthCompiler
