import Proofs.Runtime.BackendExpressionCost
import Proofs.Runtime.BackendDataSize
import Proofs.Runtime.Index
import Proofs.Runtime.Weakening
import Proofs.Runtime.BackendWeakeningSize

/-! Native cost of positional coefficient lookup. The existing executable
index scans every input cell, including the suffix after finding an entry.
The counter stays below the requested index; natural encodings and the two
natural primitives are bounded only on that reachable range. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram.IndexCompiler

universe v w

private theorem sum_rec_ite_eq {A B : Type} (p : Prop) [Decidable p]
    (f : A → Nat) (g : B → Nat) (a : A) (b : B) :
    Sum.rec f g (if p then Sum.inl a else Sum.inr b) = if p then f a else g b := by
  by_cases h : p <;> simp [h]

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
  {header : Nat} (sizes : SizeLaws Q header) (mono : Monotone overhead)

include sizes mono

theorem body_time_bound {cell : Ty Atom} {Γ : List (Ty Atom)}
    (eq : Op (.pair .nat .nat) .bool) (sub : Op (.pair .nat .nat) .nat)
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (hsub : ∀ x y, P.execute sub (x, y) = x - y)
    (x : cell.Value base) (acc : Nat × Bool × cell.Value base)
    (n : Nat) (default : cell.Value base) (xs : List (cell.Value base)) (env : Env base Γ)
    (width comparisonTime subtractTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (henv : Q.size (rep.env Γ) env ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ k ≤ n, Q.size rep.data.nat k ≤ width) (h1 : Q.size rep.data.nat 1 ≤ width)
    (hx : Q.size (rep.ty cell) x ≤ width)
    (ha : acc.1 ≤ n ∧ Q.size (rep.ty cell) acc.2.2 ≤ width)
    (hd : Q.size (rep.ty cell) default ≤ width)
    (hl : Q.size (rep.ty (.list cell)) xs ≤ width)
    (he : (primitiveBound eq).time (acc.1, 0) ≤ comparisonTime)
    (hs : (primitiveBound sub).time (acc.1, 1) ≤ subtractTime) :
    (Expression.compileBound rep data P primitive laws dataLaws primitiveBound ((indexBody eq sub).weakenTail Γ)).time
      (x, acc, n, default, xs, env) ≤ comparisonTime + subtractTime + 256 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hsum := @sizes.sum_le
  have hnat := hn n le_rfl
  have hzero := hn 0 (Nat.zero_le n)
  have hacc := hn acc.1 ha.1
  have hdecr := hn (acc.1 - 1) ((Nat.sub_le _ _).trans ha.1)
  have hleft := sizes.sum_le
    (rep.env ([cell, .pair .nat (.pair .bool cell), .nat, cell, .list cell] ++ Γ))
    (rep.env ([cell, .pair .nat (.pair .bool cell), .nat, cell, .list cell] ++ Γ))
    (.inl (x, acc, n, default, xs, env))
  have hright := sizes.sum_le
    (rep.env ([cell, .pair .nat (.pair .bool cell), .nat, cell, .list cell] ++ Γ))
    (rep.env ([cell, .pair .nat (.pair .bool cell), .nat, cell, .list cell] ++ Γ))
    (.inr (x, acc, n, default, xs, env))
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  by_cases hfound : acc.2.1 = true <;> by_cases hz : acc.1 = 0 <;>
    dsimp only [Expr.weakenTail, Var.weakenTail, List.cons_append, List.nil_append, List.append, indexBody, Expression.compileBound, Expression.variableBound,
      LocalBound.castFunction, LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
      LocalBound.identity, LocalBound.elim, DataCostLaws.unitBound, DataCostLaws.boolBound,
      DataCostLaws.natBound, DataCostLaws.selectBound, Expr.denote, Var.get,
      LanguageRepresentation.ty, LanguageRepresentation.env] <;>
    dsimp only [id, Function.comp_def, Sum.elim] <;>
    simp only [hfound, heq, hsub, hz, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false,
      sum_rec_ite_eq] <;>
    dsimp only [List.cons_append, List.nil_append, List.append, LanguageRepresentation.ty, LanguageRepresentation.env, Sum.elim] at * <;>
    clear hn heq hsub <;>
    grind only

theorem index_time_bound_of_caps {cell : Ty Atom} {Γ : List (Ty Atom)}
    (eq : Op (.pair .nat .nat) .bool) (sub : Op (.pair .nat .nat) .nat)
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (hsub : ∀ x y, P.execute sub (x, y) = x - y)
    (n : Nat) (default : cell.Value base) (xs : List (cell.Value base)) (env : Env base Γ)
    (width comparisonTime subtractTime cap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (henv : Q.size (rep.env Γ) env ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ k ≤ n, Q.size rep.data.nat k ≤ width) (h1 : Q.size rep.data.nat 1 ≤ width)
    (hd : Q.size (rep.ty cell) default ≤ width)
    (hv : ∀ x ∈ xs, Q.size (rep.ty cell) x ≤ width) (hc : xs.length ≤ cap)
    (hl : ∀ ys : List (cell.Value base), ys.length ≤ cap → (∀ y ∈ ys, y ∈ xs) →
      Q.size (rep.ty (.list cell)) ys ≤ width)
    (he : ∀ k ≤ n, (primitiveBound eq).time (k, 0) ≤ comparisonTime)
    (hs : ∀ k ≤ n, (primitiveBound sub).time (k, 1) ≤ subtractTime) :
    (Expression.compileBound rep data P primitive laws dataLaws primitiveBound ((index eq sub).weakenTail Γ)).time
      (n, default, xs, env) ≤ cap * (comparisonTime + subtractTime + 257 * overhead (128 * width)) +
        64 * overhead (128 * width) := by
  let step := fun (x : cell.Value base) (acc : Nat × Bool × cell.Value base) =>
    ((indexBody eq sub).weakenTail Γ).denote P (x, acc, n, default, xs, env)
  let inv := fun acc : Nat × Bool × cell.Value base => acc.1 ≤ n ∧ Q.size (rep.ty cell) acc.2.2 ≤ width
  have hstep (x : cell.Value base) (hx : x ∈ xs) (acc : Nat × Bool × cell.Value base) (ha : inv acc) :
      inv (step x acc) := by
    dsimp only [step]
    have hw := (indexBody (cell := cell) eq sub).weakenTail_denote (Δ := Γ) P
      (x, acc, n, default, xs, ()) env
    change ((indexBody eq sub).weakenTail Γ).denote P (x, acc, n, default, xs, env) = _ at hw
    rw [hw, indexBody_denote P eq sub heq hsub]
    dsimp only [indexStep]
    split
    · exact ha
    · split
      · exact ⟨Nat.zero_le n, hv x hx⟩
      · exact ⟨(Nat.sub_le _ _).trans ha.1, ha.2⟩
  have hfold (ys : List (cell.Value base)) (hy : ∀ y ∈ ys, y ∈ xs)
      (acc : Nat × Bool × cell.Value base) (ha : inv acc) :
      inv (ys.foldl (fun acc x => step x acc) acc) := by
    induction ys generalizing acc with
    | nil => exact ha
    | cons y ys ih =>
        exact ih (fun z hz => hy z (by simp [hz])) (step y acc) (hstep y (hy y (by simp)) acc ha)
  have hxs := hl xs hc (fun _ h => h)
  have hnat := hn n le_rfl
  have hzero := hn 0 (Nat.zero_le n)
  have hprod := @sizes.prod_le
  have hwork := foldWork_bound step
    (fun x acc => (Expression.compileBound rep data P primitive laws dataLaws primitiveBound ((indexBody eq sub).weakenTail Γ)).time
      (x, acc, n, default, xs, env))
    (foldFee (Q := Q) overhead rep.data (rep.ty cell) (rep.ty (.pair .nat (.pair .bool cell)))
      (rep.env ([.nat, cell, .list cell] ++ Γ)) (((indexBody eq sub).weakenTail Γ).denote P) (n, default, xs, env))
    (fun x => x ∈ xs) inv (comparisonTime + subtractTime + 256 * overhead (128 * width))
    (overhead (128 * width)) cap
    (by
      intro x hx acc ha
      exact ⟨body_time_bound rep data P primitive laws dataLaws primitiveBound sizes mono eq sub heq hsub
        x acc n default xs env width comparisonTime subtractTime hh hu henv hb hn h1 (hv x hx) ha hd hxs
          (he acc.1 ha.1) (hs acc.1 ha.1), hstep x hx acc ha⟩)
    (by
      intro ys hlen hys acc ha
      have hysSize := hl ys hlen hys
      have ho := hfold ys hys acc ha
      have hna := hn acc.1 ha.1
      have hno := hn (ys.foldl (fun acc x => step x acc) acc).1 ho.1
      have hba := hb acc.2.1
      have hbo := hb (ys.foldl (fun acc x => step x acc) acc).2.1
      unfold foldFee
      apply mono
      dsimp only [List.cons_append, List.nil_append, List.append, LanguageRepresentation.ty, LanguageRepresentation.env, step, inv] at *
      clear hstep hfold hn he hs heq hsub
      grind only)
    xs hc (fun _ h => h) (n, false, default) ⟨le_rfl, hd⟩
  have hout := hfold xs (fun _ h => h) (n, false, default) ⟨le_rfl, hd⟩
  have hno := hn (xs.foldl (fun acc x => step x acc) (n, false, default)).1 hout.1
  have hbo := hb (xs.foldl (fun acc x => step x acc) (n, false, default)).2.1
  have hfalse := hb false
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  have hcap := Nat.mul_le_mul_right
    (comparisonTime + subtractTime + 257 * overhead (128 * width)) hc
  dsimp only [Expr.weakenTail, Var.weakenTail, List.cons_append, List.nil_append, List.append, index, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.foldBound, DataCostLaws.unitBound, DataCostLaws.boolBound,
    Expr.denote, Var.get, LanguageRepresentation.ty, LanguageRepresentation.env, step, inv, id] at *
  clear hstep hfold hn he hs heq hsub
  grind only

include laws dataLaws

/-- The caller supplies the actual coefficient-list length, not merely the
number of transcript replies. Oversized lists are fully charged. -/
theorem index_cost_bound (lists : ListSizeLaws Q rep.data header) {cell : Ty Atom} {Γ : List (Ty Atom)}
    (eq : Op (.pair .nat .nat) .bool) (sub : Op (.pair .nat .nat) .nat)
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (hsub : ∀ x y, P.execute sub (x, y) = x - y)
    (n : Nat) (default : cell.Value base) (xs : List (cell.Value base)) (env : Env base Γ)
    (width comparisonTime subtractTime cap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (henv : Q.size (rep.env Γ) env ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ k ≤ n, Q.size rep.data.nat k ≤ width) (h1 : Q.size rep.data.nat 1 ≤ width)
    (hd : Q.size (rep.ty cell) default ≤ width)
    (hv : ∀ x ∈ xs, Q.size (rep.ty cell) x ≤ width) (hc : xs.length ≤ cap)
    (he : ∀ k ≤ n, (primitiveBound eq).time (k, 0) ≤ comparisonTime)
    (hs : ∀ k ≤ n, (primitiveBound sub).time (k, 1) ≤ subtractTime) :
    Q.cost (Expression.compile rep data P primitive ((index eq sub).weakenTail Γ)) (n, default, xs, env) ≤
      cap * (comparisonTime + subtractTime + 257 * overhead (128 * ((2 * cap + 1) * width))) +
        64 * overhead (128 * ((2 * cap + 1) * width)) := by
  have hw : width ≤ (2 * cap + 1) * width := by nlinarith
  apply (Expression.cost_compile_le rep data P primitive laws dataLaws primitiveBound ((index eq sub).weakenTail Γ)
    (n, default, xs, env)).trans
  apply index_time_bound_of_caps rep data P primitive laws dataLaws primitiveBound sizes mono eq sub heq hsub
    n default xs env ((2 * cap + 1) * width) comparisonTime subtractTime cap (hh.trans hw) (hu.trans hw) (henv.trans hw)
    (fun b => (hb b).trans hw) (fun k hk => (hn k hk).trans hw) (h1.trans hw) (hd.trans hw)
    (fun x hx => (hv x hx).trans hw) hc ?_ he hs
  intro ys hlen hys
  have hlist := lists.size_le_cap (rep.ty cell) ys width cap (fun y hy => hv y (hys y hy)) hlen
  dsimp only [LanguageRepresentation.ty] at hlist ⊢
  nlinarith [Nat.mul_le_mul_left cap hh]

omit sizes mono laws dataLaws primitiveBound [C.HasOption] in
theorem index_description {cell : Ty Atom} {Γ : List (Ty Atom)}
    (eq : Op (.pair .nat .nat) .bool) (sub : Op (.pair .nat .nat) .nat)
    (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    sizes.localSize (Expression.compile rep data P primitive ((index (cell := cell) eq sub).weakenTail Γ)) ≤
      sizes.localSize (primitive eq) + sizes.localSize (primitive sub) + 256 * allowance + 4 := by
  have h := Expression.compile_size rep data P primitive sizes allowance laws dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl)
    ((index (cell := cell) eq sub).weakenTail Γ)
  rw [Expression.descriptionBound_weakenTail] at h
  simp only [index, indexBody, Expression.descriptionBound, Expression.variableDescription] at h
  exact h.trans (by omega)

end Signatures.Runtime.BackendProgram.IndexCompiler
