import Signatures.Runtime.ListSingleton

/-! Native costs for singleton decoding. All input cells are visited; the state
has two flags and one candidate. No integer counter or atomic list-inspection
operation is assumed. -/

open PFunctor

namespace Signatures.Runtime.ListSingleton

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
  {cell : Ty Atom}

include sizes mono

theorem body_time {Γ : List (Ty Atom)} (input : Env base (cell :: stateTy cell :: Γ))
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hi : Q.size (rep.env (cell :: stateTy cell :: Γ)) input ≤ width) :
    (Expression.compileBound rep data P primitive laws dataLaws primitiveBound body).time input ≤
      128 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [body, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.unitBound, DataCostLaws.boolBound, Expr.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env, id] at *
  grind only

def frameWidth (width cap : Nat) : Nat := (4 * cap + 32) * width

def scanTime (overhead : Nat → Nat) (width cap : Nat) : Nat :=
  let fee := overhead (128 * frameWidth width cap)
  cap * (129 * fee) + 64 * fee

include lists in
theorem scan_time {Γ : List (Ty Atom)} (xs : List (cell.Value base)) (default : cell.Value base)
    (env : Env base Γ) (width cap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width) (hd : Q.size (rep.ty cell) default ≤ width)
    (hx : ∀ x ∈ xs, Q.size (rep.ty cell) x ≤ width) (hc : xs.length ≤ cap) :
    (Expression.compileBound rep data P primitive laws dataLaws primitiveBound scan).time (xs, default, env) ≤
      scanTime overhead width cap := by
  let W := frameWidth width cap
  let fee := overhead (128 * W)
  let inv := fun acc : Bool × Bool × cell.Value base => Q.size (rep.ty cell) acc.2.2 ≤ width
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hstate (acc : Bool × Bool × cell.Value base) (ha : inv acc) :
      Q.size (rep.ty (stateTy cell)) acc ≤ 5 * width := by
    have hprod := @sizes.prod_le
    dsimp only [inv, LanguageRepresentation.ty, stateTy] at *
    grind only
  have hlist (ys : List (cell.Value base)) (hl : ys.length ≤ cap)
      (hy : ∀ y ∈ ys, Q.size (rep.ty cell) y ≤ width) :
      Q.size (rep.ty (.list cell)) ys ≤ (2 * cap + 1) * width := by
    have h := lists.size_le_cap (rep.ty cell) ys width cap hy hl
    change Q.size (rep.ty (.list cell)) ys ≤ _ at h
    nlinarith [Nat.mul_le_mul_left cap hh]
  have hfold (ys : List (cell.Value base)) (hy : ∀ y ∈ ys, Q.size (rep.ty cell) y ≤ width)
      (acc : Bool × Bool × cell.Value base) (ha : inv acc) :
      inv (ys.foldl (fun acc x => step x acc) acc) := by
    induction ys generalizing acc with
    | nil => exact ha
    | cons y ys ih => exact ih (fun z hz => hy z (by simp [hz])) (step y acc) (hy y (by simp))
  have hxs := hlist xs hc hx
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have henv : Q.size (rep.env (.list cell :: cell :: Γ)) (xs, default, env) ≤ W := by
    dsimp only [W, frameWidth, LanguageRepresentation.env] at *
    grind only
  have hwork := foldWork_bound step
    (fun x acc => (Expression.compileBound rep data P primitive laws dataLaws primitiveBound
      (body (Γ := .list cell :: cell :: Γ))).time (x, acc, xs, default, env))
    (foldFee (Q := Q) overhead rep.data (rep.ty cell) (rep.ty (stateTy cell))
      (rep.env (.list cell :: cell :: Γ)) (body.denote P) (xs, default, env))
    (fun x => Q.size (rep.ty cell) x ≤ width) inv (128 * fee) fee cap
    (by
      intro x hx acc ha
      have hs := hstate acc ha
      have hi : Q.size (rep.env (cell :: stateTy cell :: .list cell :: cell :: Γ))
          (x, acc, xs, default, env) ≤ W := by
        dsimp only [W, frameWidth, LanguageRepresentation.env] at *
        grind only
      exact ⟨body_time (Γ := .list cell :: cell :: Γ) rep data P primitive laws dataLaws primitiveBound sizes mono
        (x, acc, xs, default, env) W (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) hi, hx⟩)
    (by
      intro ys hlen hys acc ha
      have hl := hlist ys hlen hys
      have hs := hstate acc ha
      have ho := hstate _ (hfold ys hys acc ha)
      unfold foldFee
      apply mono
      dsimp only [body, Expr.denote, Var.get, step, LanguageRepresentation.ty,
        LanguageRepresentation.env, W, frameWidth] at *
      grind only)
    xs hc hx (true, false, default) hd
  rw [show (step (A := cell.Value base)) = (fun x acc => (false, acc.1, x)) from rfl] at hwork
  have hinit := hstate (true, false, default) hd
  have hout := hstate _ (hfold xs hx (true, false, default) hd)
  have hfee : ∀ n ≤ 128 * W, overhead n ≤ fee := fun _ hn => mono hn
  have hcap := Nat.mul_le_mul_right (129 * fee) hc
  dsimp only [scan, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.unitBound, DataCostLaws.boolBound, DataCostLaws.foldBound,
    Expr.denote, Var.get, LanguageRepresentation.ty, LanguageRepresentation.env,
    step, id, scanTime, fee, W] at *
  dsimp only [body, Expr.denote, Var.get, step] at *
  grind only

include laws dataLaws lists in
theorem scan_cost {Γ : List (Ty Atom)} (xs : List (cell.Value base)) (default : cell.Value base)
    (env : Env base Γ) (width cap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width) (hd : Q.size (rep.ty cell) default ≤ width)
    (hx : ∀ x ∈ xs, Q.size (rep.ty cell) x ≤ width) (hc : xs.length ≤ cap) :
    Q.cost (Expression.compile rep data P primitive scan) (xs, default, env) ≤
      scanTime overhead width cap :=
  (Expression.cost_compile_le rep data P primitive laws dataLaws
    (fun instr => LocalBound.measured (primitive instr)) scan (xs, default, env)).trans
      (scan_time rep data P primitive laws dataLaws (fun instr => LocalBound.measured (primitive instr))
        sizes lists mono xs default env width cap hh hu hb he hd hx hc)

omit mono [Q.HasCategory] QP QS in
theorem output_size (xs : List (cell.Value base)) (default : cell.Value base) (width : Nat)
    (hh : header ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hd : Q.size (rep.ty cell) default ≤ width) (hx : ∀ x ∈ xs, Q.size (rep.ty cell) x ≤ width) :
    Q.size (rep.ty (.pair .bool cell)) (value default xs) ≤ 3 * width := by
  have h := sizes.prod_le rep.data.bool (rep.ty cell) (value default xs)
  have hflag := hb (value default xs).1
  have hval := value_property (fun x => Q.size (rep.ty cell) x ≤ width) default xs hd hx
  exact h.trans (by omega)

omit sizes mono [C.HasOption] in
theorem description {Γ : List (Ty Atom)} (descriptionSize : DescriptionSize Q) (allowance : Nat)
    (dlaws : LocalDescriptionLaws descriptionSize allowance)
    (dataDescription : DataDescriptionLaws descriptionSize rep.data data allowance) :
    descriptionSize.localSize (Expression.compile rep data P primitive (scan (cell := cell) (Γ := Γ))) ≤
      128 * allowance := by
  have h := Expression.compile_size rep data P primitive descriptionSize allowance dlaws dataDescription
    (fun instr => descriptionSize.localSize (primitive instr)) (fun _ => le_rfl) (scan (cell := cell) (Γ := Γ))
  refine h.trans ?_
  simp only [scan, body, Expression.descriptionBound, Expression.variableDescription]
  omega

end Signatures.Runtime.ListSingleton
