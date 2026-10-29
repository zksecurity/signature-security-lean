import Proofs.Runtime.BackendCallerCost
import Proofs.Runtime.GeneralSyncWrapCaps

/-! # Structural costs at one frame width

Every structural law charges `overhead` at the encoded sizes of the values it touches. When all
of them are below one frame width `W`, each charge is at most one `fee`, the overhead at three
frames. Stating the laws this way lets a wiring's cost be read off as the sum of its leaf costs
plus one fee per structural node, with the size facts supplied once per value. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram.FrameCost

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dispatch : DispatchCostLaws (Q := Q) overhead)
  (optLaws : SyncWrapGeneral.OptionCostLaws (Q := Q) overhead)
  {data : DataRepresentation C} {code : DataCode Q data} (dataLaws : DataCostLaws data code overhead)
  (mono : Monotone overhead)

local notation "prod" => StepClass.HasProd.prod
local notation "sum" => StepClass.HasSum.sum
local notation "opt" => StepClass.HasOption.option

/-- One structural charge at the frame. -/
def fee (overhead : Nat → Nat) (W : Nat) : Nat := overhead (3 * W)

variable (W : Nat)

include mono

include laws in
omit [C.HasOption] QO QD OC in
theorem compose_le {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D} {f : A → B} {g : B → D}
    (left : Q.Realizer a b f) (right : Q.Realizer b d g) (x : A) {Tl Tr : Nat}
    (hl : Q.cost left x ≤ Tl) (hr : Q.cost right (f x) ≤ Tr)
    (hx : Q.size a x ≤ W) (hfx : Q.size b (f x) ≤ W) (hgx : Q.size d (g (f x)) ≤ W) :
    Q.cost (Q.compose left right) x ≤ Tl + Tr + fee overhead W := by
  have h := laws.compose left right x
  have hm : overhead (Q.size a x + Q.size b (f x) + Q.size d (g (f x))) ≤ fee overhead W := mono (by omega)
  omega

include laws in
omit [C.HasOption] QO QD OC in
theorem pair_le {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D} {f : A → B} {g : A → D}
    (left : Q.Realizer a b f) (right : Q.Realizer a d g) (x : A) {Tl Tr : Nat}
    (hl : Q.cost left x ≤ Tl) (hr : Q.cost right x ≤ Tr)
    (hx : Q.size a x ≤ W) (hp : Q.size (prod b d) (f x, g x) ≤ W) :
    Q.cost (QP.pair left right) x ≤ Tl + Tr + fee overhead W := by
  have h := laws.pair left right x
  have hm : overhead (Q.size a x + Q.size (prod b d) (f x, g x)) ≤ fee overhead W := mono (by omega)
  omega

include laws in
omit [C.HasOption] QO QD OC in
theorem fst_le {A B : Type} (a : C.Str A) (b : C.Str B) (x : A × B)
    (hx : Q.size (prod a b) x ≤ W) (h1 : Q.size a x.1 ≤ W) :
    Q.cost (QP.fst a b) x ≤ fee overhead W :=
  (laws.fst a b x).trans (mono (by omega))

include laws in
omit [C.HasOption] QO QD OC in
theorem snd_le {A B : Type} (a : C.Str A) (b : C.Str B) (x : A × B)
    (hx : Q.size (prod a b) x ≤ W) (h2 : Q.size b x.2 ≤ W) :
    Q.cost (QP.snd a b) x ≤ fee overhead W :=
  (laws.snd a b x).trans (mono (by omega))

include laws in
omit [C.HasOption] QO QD OC in
theorem identity_le {A : Type} (a : C.Str A) (x : A) (hx : Q.size a x ≤ W) :
    Q.cost (Q.identity a) x ≤ fee overhead W :=
  (laws.identity a x).trans (mono (by omega))

include laws in
omit [C.HasOption] QO QD OC in
theorem elim_inl_le {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D} {f : A → D} {g : B → D}
    (left : Q.Realizer a d f) (right : Q.Realizer b d g) (x : A) {T : Nat}
    (hl : Q.cost left x ≤ T) (hx : Q.size (sum a b) (.inl x) ≤ W) (hres : Q.size d (f x) ≤ W) :
    Q.cost (QS.elim left right) (.inl x) ≤ T + fee overhead W := by
  have h := laws.elim left right (.inl x)
  simp only [Sum.elim_inl] at h
  have hm : overhead (Q.size (sum a b) (Sum.inl x) + Q.size d (f x)) ≤ fee overhead W := mono (by omega)
  omega

include laws in
omit [C.HasOption] QO QD OC in
theorem elim_inr_le {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D} {f : A → D} {g : B → D}
    (left : Q.Realizer a d f) (right : Q.Realizer b d g) (x : B) {T : Nat}
    (hr : Q.cost right x ≤ T) (hx : Q.size (sum a b) (.inr x) ≤ W) (hres : Q.size d (g x) ≤ W) :
    Q.cost (QS.elim left right) (.inr x) ≤ T + fee overhead W := by
  have h := laws.elim left right (.inr x)
  simp only [Sum.elim_inr] at h
  have hm : overhead (Q.size (sum a b) (Sum.inr x) + Q.size d (g x)) ≤ fee overhead W := mono (by omega)
  omega

include dispatch in
omit [Q.HasCategory] QP in
theorem inl_le {A B : Type} (a : C.Str A) (b : C.Str B) (x : A)
    (hx : Q.size a x ≤ W) (hs : Q.size (sum a b) (.inl x) ≤ W) :
    Q.cost (QS.inl a b) x ≤ fee overhead W :=
  (dispatch.inl a b x).trans (mono (by omega))

include dispatch in
omit [Q.HasCategory] QP in
theorem inr_le {A B : Type} (a : C.Str A) (b : C.Str B) (x : B)
    (hx : Q.size b x ≤ W) (hs : Q.size (sum a b) (.inr x) ≤ W) :
    Q.cost (QS.inr a b) x ≤ fee overhead W :=
  (dispatch.inr a b x).trans (mono (by omega))

include dispatch in
omit [Q.HasCategory] QP in
theorem none_le {A B : Type} (a : C.Str A) (b : C.Str B) (x : A)
    (hx : Q.size a x ≤ W) (hn : Q.size (opt b) none ≤ W) :
    Q.cost (QO.none a b) x ≤ fee overhead W :=
  (dispatch.none a b x).trans (mono (by omega))

include dispatch in
omit [Q.HasCategory] QP in
theorem some_le {A : Type} (a : C.Str A) (x : A)
    (hx : Q.size a x ≤ W) (hs : Q.size (opt a) (some x) ≤ W) :
    Q.cost (OC.someCode a) x ≤ fee overhead W :=
  (dispatch.some a x).trans (mono (by omega))

include dispatch in
omit [Q.HasCategory] QP in
theorem distribute_le {A B E : Type} (a : C.Str A) (b : C.Str B) (e : C.Str E) (x : (A ⊕ B) × E)
    (hx : Q.size (prod (sum a b) e) x ≤ W)
    (hr : Q.size (sum (prod a e) (prod b e))
      (Sum.elim (fun left => Sum.inl (left, x.2)) (fun right => Sum.inr (right, x.2)) x.1) ≤ W) :
    Q.cost (QD.distribute a b e) x ≤ fee overhead W :=
  (dispatch.distribute a b e x).trans (mono (by omega))

include dataLaws in
omit [C.HasOption] [Q.HasCategory] QP QS QO QD OC in
theorem select_le {A : Type} (a : C.Str A) (x : Bool × A)
    (hx : Q.size (prod data.bool a) x ≤ W)
    (hr : Q.size (sum a a) (if x.1 = true then Sum.inl x.2 else Sum.inr x.2) ≤ W) :
    Q.cost (code.select a) x ≤ fee overhead W :=
  (dataLaws.select a x).trans (mono (by omega))

include dataLaws in
omit [C.HasOption] [Q.HasCategory] QP QS QO QD OC in
theorem unit_le {A : Type} (a : C.Str A) (x : A) (hx : Q.size a x ≤ W) (hu : Q.size data.unit () ≤ W) :
    Q.cost (code.unit a) x ≤ fee overhead W :=
  (dataLaws.unit a x).trans (mono (by omega))

include dataLaws in
omit [C.HasOption] [Q.HasCategory] QP QS QO QD OC in
theorem bool_le (value : Bool) (hu : Q.size data.unit () ≤ W) (hb : Q.size data.bool value ≤ W) :
    Q.cost (code.bool value) () ≤ fee overhead W :=
  (dataLaws.bool value ()).trans (mono (by omega))

include dataLaws in
omit [C.HasOption] [Q.HasCategory] QP QS QO QD OC in
theorem nil_le {A : Type} (a : C.Str A) (hu : Q.size data.unit () ≤ W) (hn : Q.size (data.list a) [] ≤ W) :
    Q.cost (code.nil a) () ≤ fee overhead W :=
  (dataLaws.nil a ()).trans (mono (by omega))

include dataLaws in
omit [C.HasOption] [Q.HasCategory] QP QS QO QD OC in
theorem cons_le {A : Type} (a : C.Str A) (x : A × List A)
    (hx : Q.size (prod a (data.list a)) x ≤ W) (hr : Q.size (data.list a) (x.1 :: x.2) ≤ W) :
    Q.cost (code.cons a) x ≤ fee overhead W :=
  (dataLaws.cons a x).trans (mono (by omega))

include optLaws in
omit [C.HasSum] [Q.HasCategory] QP QS QD OC in
theorem map_le {A B : Type} {a : C.Str A} {b : C.Str B} {f : A → B} (inner : Q.Realizer a b f) (x : Option A) {T : Nat}
    (hinner : ∀ v, x = some v → Q.cost inner v ≤ T)
    (hx : Q.size (opt a) x ≤ W) (hr : Q.size (opt b) (x.map f) ≤ W) :
    Q.cost (QO.map inner) x ≤ T + fee overhead W := by
  have hm : overhead (Q.size (opt a) x + Q.size (opt b) (x.map f)) ≤ fee overhead W := mono (by omega)
  refine (optLaws.map inner x).trans ?_
  cases x with
  | none =>
    show 0 + overhead (Q.size (opt a) none + Q.size (opt b) (Option.map f none)) ≤ T + fee overhead W
    omega
  | some v =>
    have := hinner v rfl
    show Q.cost inner v + overhead (Q.size (opt a) (some v) + Q.size (opt b) (Option.map f (some v))) ≤ T + fee overhead W
    omega

include optLaws in
omit [C.HasSum] [Q.HasCategory] QP QS QD OC in
theorem bindContext_le {A B E : Type} {a : C.Str A} {b : C.Str B} {e : C.Str E} {k : A × E → Option B}
    (inner : Q.Realizer (prod a e) (opt b) k) (x : Option A × E) {T : Nat}
    (hinner : ∀ v, x.1 = some v → Q.cost inner (v, x.2) ≤ T)
    (hx : Q.size (prod (opt a) e) x ≤ W) (hr : Q.size (opt b) (x.1.bind fun v => k (v, x.2)) ≤ W) :
    Q.cost (QO.bindContext inner) x ≤ T + fee overhead W := by
  obtain ⟨o, ctx⟩ := x
  dsimp only at hinner hx hr
  refine (optLaws.bindContext inner (o, ctx)).trans ?_
  cases o with
  | none =>
    have hm : overhead (Q.size (prod (opt a) e) ((none : Option A), ctx) +
        Q.size (opt b) ((none : Option A).bind fun v => k (v, ctx))) ≤ fee overhead W := mono (by omega)
    show 0 + overhead (Q.size (prod (opt a) e) ((none : Option A), ctx) +
      Q.size (opt b) ((none : Option A).bind fun v => k (v, ctx))) ≤ T + fee overhead W
    omega
  | some v =>
    have := hinner v rfl
    have hm : overhead (Q.size (prod (opt a) e) (some v, ctx) +
        Q.size (opt b) ((some v).bind fun v => k (v, ctx))) ≤ fee overhead W := mono (by omega)
    show Q.cost inner (v, ctx) + overhead (Q.size (prod (opt a) e) (some v, ctx) +
      Q.size (opt b) ((some v).bind fun v => k (v, ctx))) ≤ T + fee overhead W
    omega

omit mono [C.HasProd] [C.HasSum] [C.HasOption] [Q.HasCategory] QP QS QO QD OC in
theorem castFunction_le {A B : Type} {a : C.Str A} {b : C.Str B} {f g : A → B} (inner : Q.Realizer a b f) (h : f = g)
    (x : A) {T : Nat} (hc : Q.cost inner x ≤ T) : Q.cost (inner.castFunction h) x ≤ T := by
  rwa [QuantitativeStepClass.Realizer.cost_castFunction]

end Signatures.Runtime.BackendProgram.FrameCost
