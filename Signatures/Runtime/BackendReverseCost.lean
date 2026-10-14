import Signatures.Runtime.BackendFoldGrowth
import Signatures.Runtime.BackendExpressionCost
import Signatures.Runtime.BackendExpressionSize
import Signatures.Runtime.BackendDataSize
import Signatures.Runtime.Sampling

/-! The native implementation of transcript reversal is the existing cons fold.
The remaining-input invariant bounds its growing result and retained environment;
all list construction, copying, traversal, and final fold fees are charged. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram.ReverseCompiler

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

include sizes lists mono

theorem body_time_bound {cell : Ty Atom} {Γ : List (Ty Atom)}
    (env : Env base (cell :: .list cell :: Γ)) (width : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env (cell :: .list cell :: Γ)) env ≤ width) :
    (Expression.compileBound rep data P primitive laws dataLaws primitiveBound
      (.cons (.var .here) (.var (.there .here)) : Expr Op (cell :: .list cell :: Γ) (.list cell))).time env ≤
      16 * overhead (32 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcons := @lists.cons_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, DataCostLaws.consBound,
    Expr.denote, Var.get, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  grind only

theorem reverse_time_bound {cell : Ty Atom} {Γ : List (Ty Atom)}
    (xs : List (cell.Value base)) (env : Env base Γ) (width cap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width)
    (hv : ∀ x ∈ xs, Q.size (rep.ty cell) x ≤ width) (hc : xs.length ≤ cap) :
    (Expression.compileBound rep data P primitive laws dataLaws primitiveBound
      (reverseList (cell := cell) (Γ := Γ))).time (xs, env) ≤
        cap * (17 * overhead (128 * ((4 * cap + 8) * width))) +
          16 * overhead (128 * ((4 * cap + 8) * width)) := by
  let W := (4 * cap + 8) * width
  let fee := overhead (128 * W)
  let step := fun (x : cell.Value base) (acc : List (cell.Value base)) => x :: acc
  let inv := fun remaining (acc : List (cell.Value base)) =>
    acc.length + remaining ≤ cap ∧ ∀ x ∈ acc, Q.size (rep.ty cell) x ≤ width
  have hw : width ≤ W := by dsimp [W]; nlinarith
  have hlist (ys : List (cell.Value base)) (hl : ys.length ≤ cap)
      (hy : ∀ y ∈ ys, Q.size (rep.ty cell) y ≤ width) :
      Q.size (rep.ty (.list cell)) ys ≤ (2 * cap + 1) * width := by
    have h := lists.size_le_cap (rep.ty cell) ys width cap hy hl
    change Q.size (rep.ty (.list cell)) ys ≤ _ at h
    nlinarith [Nat.mul_le_mul_left cap hh]
  have hxs := hlist xs hc hv
  have hfold (ys acc : List (cell.Value base)) (hy : ∀ y ∈ ys, Q.size (rep.ty cell) y ≤ width)
      (ha : inv ys.length acc) : inv 0 (ys.foldl (fun acc x => step x acc) acc) := by
    induction ys generalizing acc with
    | nil => exact ha
    | cons y ys ih =>
        apply ih (step y acc) (fun z hz => hy z (by simp [hz]))
        exact ⟨by dsimp only [step]; simp only [List.length_cons] at *; dsimp only [inv] at ha; omega,
          by intro z hz; rcases List.mem_cons.mp hz with hz | hz
             · subst z; exact hy y (by simp)
             · exact ha.2 z hz⟩
  have hprod := @sizes.prod_le
  have henv : Q.size (rep.env (.list cell :: Γ)) (xs, env) ≤ (2 * cap + 3) * width := by
    have h := sizes.prod_le (rep.ty (.list cell)) (rep.env Γ) (xs, env)
    dsimp only [LanguageRepresentation.env] at *
    nlinarith
  have hwork := foldWork_bound_remaining step
    (fun x acc => (Expression.compileBound rep data P primitive laws dataLaws primitiveBound
      (.cons (.var .here) (.var (.there .here)) : Expr Op (cell :: .list cell :: .list cell :: Γ) (.list cell))).time
        (x, acc, xs, env))
    (foldFee (Q := Q) overhead rep.data (rep.ty cell) (rep.ty (.list cell)) (rep.env (.list cell :: Γ))
      (fun p => p.1 :: p.2.1) (xs, env))
    (fun x => x ∈ xs) inv (16 * fee) fee cap
    (by
      intro remaining hremaining x hx acc ha
      have haSize := hlist acc (by have := ha.1; omega) ha.2
      have hxSize := hv x hx
      have hroot : Q.size (rep.env (cell :: .list cell :: .list cell :: Γ)) (x, acc, xs, env) ≤ W := by
        dsimp only [LanguageRepresentation.env] at *
        dsimp only [W]
        grind only
      have ht := body_time_bound rep data P primitive laws dataLaws primitiveBound sizes lists mono
        (Γ := .list cell :: Γ) (x, acc, xs, env) W (hh.trans hw) hroot
      have hf : overhead (32 * W) ≤ fee := mono (by omega)
      refine ⟨by omega, ?_⟩
      exact ⟨by dsimp only [step]; simp only [List.length_cons]; have := ha.1; omega,
        by intro y hy; rcases List.mem_cons.mp hy with rfl | hy
           · exact hxSize
           · exact ha.2 y hy⟩)
    (by
      intro ys hlen hys acc ha
      have hysSize := hlist ys hlen (fun y hy => hv y (hys y hy))
      have haSize := hlist acc (by have := ha.1; omega) ha.2
      have ho := hfold ys acc (fun y hy => hv y (hys y hy)) ha
      have hoSize := hlist (ys.foldl (fun acc x => step x acc) acc) (by have := ho.1; omega) ho.2
      unfold foldFee
      apply mono
      dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env, step, fee, W] at *
      grind only)
    xs hc (fun _ h => h) [] ⟨by simpa, by simp⟩
  have hnil := lists.nil_le (rep.ty cell)
  have ho := hfold xs [] hv ⟨by simpa, by simp⟩
  have hout := hlist (xs.foldl (fun acc x => step x acc) []) (by have := ho.1; omega) ho.2
  have hfee : ∀ n ≤ 128 * W, overhead n ≤ fee := fun _ hn => mono hn
  have hcap := Nat.mul_le_mul_right (17 * fee) hc
  dsimp only [reverseList, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.foldBound, DataCostLaws.unitBound, DataCostLaws.nilBound,
    Expr.denote, Var.get, LanguageRepresentation.ty, LanguageRepresentation.env, step, id, fee, W] at *
  grind only

include laws dataLaws primitiveBound in
theorem reverse_cost_bound {cell : Ty Atom} {Γ : List (Ty Atom)}
    (xs : List (cell.Value base)) (env : Env base Γ) (width cap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width)
    (hv : ∀ x ∈ xs, Q.size (rep.ty cell) x ≤ width) (hc : xs.length ≤ cap) :
    Q.cost (Expression.compile rep data P primitive (reverseList (cell := cell) (Γ := Γ))) (xs, env) ≤
      cap * (17 * overhead (128 * ((4 * cap + 8) * width))) +
        16 * overhead (128 * ((4 * cap + 8) * width)) :=
  (Expression.cost_compile_le rep data P primitive laws dataLaws primitiveBound _ _).trans
    (reverse_time_bound rep data P primitive laws dataLaws primitiveBound sizes lists mono xs env
      width cap hh hu he hv hc)

omit sizes lists mono laws dataLaws primitiveBound [C.HasOption] in
theorem reverse_description {cell : Ty Atom} {Γ : List (Ty Atom)}
    (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    sizes.localSize (Expression.compile rep data P primitive (reverseList (cell := cell) (Γ := Γ))) ≤
      16 * allowance := by
  have h := Expression.compile_size rep data P primitive sizes allowance laws dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl)
    (reverseList (cell := cell) (Γ := Γ))
  simp only [reverseList, Expression.descriptionBound, Expression.variableDescription] at h
  exact h.trans (by omega)

end Signatures.Runtime.BackendProgram.ReverseCompiler
