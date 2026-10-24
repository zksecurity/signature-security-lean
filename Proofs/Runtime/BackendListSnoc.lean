import Proofs.Runtime.ListSnoc

/-! Costs of chronological history append, including both traversals and the
retained original environment. The public cost bound contains no primitive or
completed-append efficiency premise: only ordinary list/structural contracts. -/

open PFunctor

namespace Signatures.Runtime.ListSnoc

open BackendProgram

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
  {cell : Ty Atom} {Γ : List (Ty Atom)}

include sizes lists mono

private theorem withReversals_time
    (first : Expr Op (.list cell :: cell :: .list cell :: Γ) (.list cell))
    (second : Expr Op (.list cell :: .list cell :: .list cell :: cell :: .list cell :: Γ) (.list cell))
    (x : cell.Value base) (xs : List (cell.Value base)) (env : Env base Γ)
    (width firstTime secondTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env (cell :: .list cell :: Γ)) (x, xs, env) ≤ width)
    (hfirst : Q.size (rep.ty (.list cell)) (first.denote P (xs, x, xs, env)) ≤ width)
    (hsecond : Q.size (rep.ty (.list cell))
      (second.denote P (x :: first.denote P (xs, x, xs, env), first.denote P (xs, x, xs, env), xs, x, xs, env)) ≤ width)
    (ht : (Expression.compileBound rep data P primitive laws dataLaws primitiveBound first).time
      (xs, x, xs, env) ≤ firstTime)
    (hu : (Expression.compileBound rep data P primitive laws dataLaws primitiveBound second).time
      (x :: first.denote P (xs, x, xs, env), first.denote P (xs, x, xs, env), xs, x, xs, env) ≤ secondTime) :
    (Expression.compileBound rep data P primitive laws dataLaws primitiveBound (withReversals first second)).time
      (x, xs, env) ≤ firstTime + secondTime + 64 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcons := @lists.cons_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [withReversals, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.consBound, Expr.denote, Var.get, id, Function.comp_def,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

def frameWidth (width cap : Nat) : Nat := (8 * cap + 32) * width

def snocTime (overhead : Nat → Nat) (width cap : Nat) : Nat :=
  (34 * cap + 113) * overhead (128 * ((4 * cap + 12) * frameWidth width cap))

theorem expression_time (x : cell.Value base) (xs : List (cell.Value base)) (env : Env base Γ)
    (width cap : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width) (hx : Q.size (rep.ty cell) x ≤ width)
    (hv : ∀ y ∈ xs, Q.size (rep.ty cell) y ≤ width) (hc : xs.length ≤ cap) :
    (Expression.compileBound rep data P primitive laws dataLaws primitiveBound expression).time
      (x, xs, env) ≤ snocTime overhead width cap := by
  let W := frameWidth width cap
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hlist (ys : List (cell.Value base)) (hys : ys.length ≤ cap + 1)
      (hv : ∀ y ∈ ys, Q.size (rep.ty cell) y ≤ width) :
      Q.size (rep.ty (.list cell)) ys ≤ (2 * cap + 3) * width := by
    have h := lists.size_le_cap (rep.ty cell) ys width (cap + 1) hv hys
    change Q.size (rep.ty (.list cell)) ys ≤ _ at h
    have hheader := Nat.mul_le_mul_left (cap + 1) hh
    nlinarith
  have hr : ∀ y ∈ xs.reverse, Q.size (rep.ty cell) y ≤ width := fun y hy => hv y (List.mem_reverse.mp hy)
  have hy : ∀ y ∈ x :: xs.reverse, Q.size (rep.ty cell) y ≤ width := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact hr y hy
  have hxs := hlist xs (by omega) hv
  have hrev := hlist xs.reverse (by simp only [List.length_reverse]; omega) hr
  have hout := hlist (x :: xs.reverse).reverse (by simp only [List.length_reverse, List.length_cons]; omega)
    (fun y hy' => hy y (List.mem_reverse.mp hy'))
  have hp := @sizes.prod_le
  have hin : Q.size (rep.env (cell :: .list cell :: Γ)) (x, xs, env) ≤ W := by
    dsimp only [LanguageRepresentation.env, W, frameWidth] at *
    grind only
  have hcontext : Q.size (rep.env (.list cell :: .list cell :: cell :: .list cell :: Γ))
      (xs.reverse, xs, x, xs, env) ≤ W := by
    dsimp only [LanguageRepresentation.env, W, frameWidth] at *
    grind only
  have hfirst := ReverseCompiler.reverse_time_bound (cell := cell) (Γ := cell :: .list cell :: Γ)
    rep data P primitive laws dataLaws primitiveBound sizes lists mono
    xs (x, xs, env) W cap (hh.trans hw) (hu.trans hw) hin (fun y hy => (hv y hy).trans hw) hc
  have hsecond := ReverseCompiler.reverse_time_bound (cell := cell) (Γ := .list cell :: .list cell :: cell :: .list cell :: Γ)
    rep data P primitive laws dataLaws primitiveBound sizes lists mono
    (x :: xs.reverse) (xs.reverse, xs, x, xs, env) W (cap + 1) (hh.trans hw) (hu.trans hw) hcontext
    (fun y hy' => (hy y hy').trans hw) (by simp only [List.length_cons, List.length_reverse]; omega)
  have hdenote := reverseList_denote (cell := cell) (Γ := cell :: .list cell :: Γ) P xs (x, xs, env)
  have ht := withReversals_time (cell := cell) (Γ := Γ)
    rep data P primitive laws dataLaws primitiveBound sizes lists mono
    reverseList reverseList x xs env W
    (cap * (17 * overhead (128 * ((4 * cap + 8) * W))) + 16 * overhead (128 * ((4 * cap + 8) * W)))
    ((cap + 1) * (17 * overhead (128 * ((4 * (cap + 1) + 8) * W))) +
      16 * overhead (128 * ((4 * (cap + 1) + 8) * W)))
    (hh.trans hw) hin
    (by rw [reverseList_denote]; exact hrev.trans (by dsimp [W, frameWidth]; nlinarith))
    (by rw [reverseList_denote, reverseList_denote]; exact hout.trans (by dsimp [W, frameWidth]; nlinarith))
    hfirst (by rw [hdenote]; exact hsecond)
  have hf₁ := mono (show 128 * ((4 * cap + 8) * W) ≤ 128 * ((4 * cap + 12) * W) by nlinarith)
  have hf₂ := mono (show 128 * W ≤ 128 * ((4 * cap + 12) * W) by nlinarith)
  have hscale : 128 * ((4 * (cap + 1) + 8) * W) = 128 * ((4 * cap + 12) * W) := by ring
  rw [hscale] at ht
  have hmul := Nat.mul_le_mul_left (cap * 17 + 16) hf₁
  have htail := Nat.mul_le_mul_left 64 hf₂
  exact ht.trans (by dsimp only [snocTime, W] at *; nlinarith)

include laws dataLaws in
theorem cost (x : cell.Value base) (xs : List (cell.Value base)) (env : Env base Γ)
    (width cap : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width) (hx : Q.size (rep.ty cell) x ≤ width)
    (hv : ∀ y ∈ xs, Q.size (rep.ty cell) y ≤ width) (hc : xs.length ≤ cap) :
    Q.cost (Expression.compile rep data P primitive expression) (x, xs, env) ≤ snocTime overhead width cap :=
  (Expression.cost_compile_le rep data P primitive laws dataLaws (fun op => LocalBound.measured (primitive op))
    expression (x, xs, env)).trans
      (expression_time rep data P primitive laws dataLaws (fun op => LocalBound.measured (primitive op))
        sizes lists mono x xs env width cap hh hu he hx hv hc)

omit sizes lists mono [C.HasOption] in
theorem description (descriptionSize : DescriptionSize Q) (allowance : Nat)
    (dlaws : LocalDescriptionLaws descriptionSize allowance)
    (dataDescription : DataDescriptionLaws descriptionSize rep.data data allowance) :
    descriptionSize.localSize (Expression.compile rep data P primitive (expression (cell := cell) (Γ := Γ))) ≤
      96 * allowance := by
  have h := Expression.compile_size rep data P primitive descriptionSize allowance dlaws dataDescription
    (fun op => descriptionSize.localSize (primitive op)) (fun _ => le_rfl) (expression (cell := cell) (Γ := Γ))
  refine h.trans ?_
  simp only [expression, withReversals, reverseList, Expression.descriptionBound, Expression.variableDescription]
  omega

end Signatures.Runtime.ListSnoc
