import Signatures.Runtime.ListEmpty

/-! Native costs of emptiness detection. The bound uses encountered cells,
their widths and the retained context; no atomic list-inspection is assumed. -/

open PFunctor

namespace Signatures.Runtime.ListEmpty

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

def frameWidth (width cap : Nat) : Nat := (2 * cap + 16) * width

def scanTime (overhead : Nat → Nat) (width cap : Nat) : Nat :=
  (17 * cap + 32) * overhead (128 * frameWidth width cap)

include sizes lists mono

theorem scan_time (xs : List (cell.Value base)) (env : Env base Γ) (width cap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width)
    (hx : ∀ x ∈ xs, Q.size (rep.ty cell) x ≤ width) (hc : xs.length ≤ cap) :
    (Expression.compileBound rep data P primitive laws dataLaws primitiveBound scan).time (xs, env) ≤
      scanTime overhead width cap := by
  let W := frameWidth width cap
  let fee := overhead (128 * W)
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hlist (ys : List (cell.Value base)) (hl : ys.length ≤ cap)
      (hy : ∀ y ∈ ys, Q.size (rep.ty cell) y ≤ width) :
      Q.size (rep.ty (.list cell)) ys ≤ (2 * cap + 1) * width := by
    have h := lists.size_le_cap (rep.ty cell) ys width cap hy hl
    change Q.size (rep.ty (.list cell)) ys ≤ _ at h
    nlinarith [Nat.mul_le_mul_left cap hh]
  have hxs := hlist xs hc hx
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have henv : Q.size (rep.env (.list cell :: Γ)) (xs, env) ≤ W := by
    dsimp only [W, frameWidth, LanguageRepresentation.env] at *
    grind only
  have hwork := foldWork_bound (fun (_ : cell.Value base) (_ : Bool) => false)
    (fun x acc => (Expression.compileBound rep data P primitive laws dataLaws primitiveBound
      (.bool false : Expr Op (cell :: .bool :: .list cell :: Γ) .bool)).time (x, acc, xs, env))
    (foldFee (Q := Q) overhead rep.data (rep.ty cell) rep.data.bool (rep.env (.list cell :: Γ))
      (fun _ => false) (xs, env))
    (fun x => Q.size (rep.ty cell) x ≤ width) (fun _ => True) (16 * fee) fee cap
    (by
      intro x hx acc _
      have hi : Q.size (rep.env (cell :: .bool :: .list cell :: Γ)) (x, acc, xs, env) ≤ W := by
        dsimp only [W, frameWidth, LanguageRepresentation.env, LanguageRepresentation.ty] at *
        grind only
      refine ⟨?_, True.intro⟩
      have hfee : ∀ n ≤ 128 * W, overhead n ≤ fee := fun _ hn => mono hn
      dsimp only [Expression.compileBound, LocalBound.compose, DataCostLaws.unitBound,
        DataCostLaws.boolBound, LanguageRepresentation.ty, LanguageRepresentation.env] at *
      grind only)
    (by
      intro ys hlen hys acc _
      have hl := hlist ys hlen hys
      unfold foldFee
      apply mono
      dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env, W, frameWidth] at *
      grind only)
    xs hc hx true True.intro
  have hfee : ∀ n ≤ 128 * W, overhead n ≤ fee := fun _ hn => mono hn
  have hcap := Nat.mul_le_mul_right (17 * fee) hc
  dsimp only [scan, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.unitBound, DataCostLaws.boolBound, DataCostLaws.foldBound,
    Expr.denote, Var.get, LanguageRepresentation.ty, LanguageRepresentation.env, id, scanTime, fee, W] at *
  grind only

include laws dataLaws in
theorem cost (xs : List (cell.Value base)) (env : Env base Γ) (width cap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (he : Q.size (rep.env Γ) env ≤ width)
    (hx : ∀ x ∈ xs, Q.size (rep.ty cell) x ≤ width) (hc : xs.length ≤ cap) :
    Q.cost (Expression.compile rep data P primitive scan) (xs, env) ≤ scanTime overhead width cap :=
  (Expression.cost_compile_le rep data P primitive laws dataLaws (fun instr => LocalBound.measured (primitive instr))
    scan (xs, env)).trans
      (scan_time rep data P primitive laws dataLaws (fun instr => LocalBound.measured (primitive instr))
        sizes lists mono xs env width cap hh hu hb he hx hc)

omit sizes lists mono [C.HasOption] in
theorem description (descriptionSize : DescriptionSize Q) (allowance : Nat)
    (dlaws : LocalDescriptionLaws descriptionSize allowance)
    (dataDescription : DataDescriptionLaws descriptionSize rep.data data allowance) :
    descriptionSize.localSize (Expression.compile rep data P primitive (scan (cell := cell) (Γ := Γ))) ≤
      16 * allowance := by
  have h := Expression.compile_size rep data P primitive descriptionSize allowance dlaws dataDescription
    (fun instr => descriptionSize.localSize (primitive instr)) (fun _ => le_rfl) (scan (cell := cell) (Γ := Γ))
  refine h.trans ?_
  simp only [scan, Expression.descriptionBound, Expression.variableDescription]
  omega

end Signatures.Runtime.ListEmpty
