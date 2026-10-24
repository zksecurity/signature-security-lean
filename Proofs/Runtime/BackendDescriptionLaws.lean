import Proofs.Runtime.BackendExpression

/-! Static description contracts for individual code constructors. These are
separate from runtime/encoded-value laws. The allowance may depend on the chosen
representation and security parameter; no constant-size physical implementation
or polynomial family bound is asserted here. Literal values and executable fold
bodies are explicitly counted. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}

omit [C.HasProd] [C.HasSum] in
theorem DescriptionSize.castFunction (sizes : DescriptionSize Q)
    {A B : Type} {a : C.Str A} {b : C.Str B} {f g : A → B}
    (code : Q.Realizer a b f) (h : f = g) :
    sizes.localSize (code.castFunction h) = sizes.localSize code := by
  cases h
  rfl

structure LocalDescriptionLaws (sizes : DescriptionSize Q) [Q.HasCategory]
    [QP : Q.HasProd] [QS : Q.HasSum] (allowance : Nat) : Prop where
  identity : ∀ {A : Type} (a : C.Str A), sizes.localSize (Q.identity a) ≤ allowance
  compose : ∀ {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : B → D} (left : Q.Realizer a b f) (right : Q.Realizer b d g),
    sizes.localSize (Q.compose left right) ≤ sizes.localSize left + sizes.localSize right + allowance
  fst : ∀ {A B : Type} (a : C.Str A) (b : C.Str B), sizes.localSize (QP.fst a b) ≤ allowance
  snd : ∀ {A B : Type} (a : C.Str A) (b : C.Str B), sizes.localSize (QP.snd a b) ≤ allowance
  pair : ∀ {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : A → D} (left : Q.Realizer a b f) (right : Q.Realizer a d g),
    sizes.localSize (QP.pair left right) ≤ sizes.localSize left + sizes.localSize right + allowance
  elim : ∀ {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → D} {g : B → D} (left : Q.Realizer a d f) (right : Q.Realizer b d g),
    sizes.localSize (QS.elim left right) ≤ sizes.localSize left + sizes.localSize right + allowance

structure DataDescriptionLaws (sizes : DescriptionSize Q)
    (data : DataRepresentation C) (code : DataCode Q data) (allowance : Nat) : Prop where
  unit : ∀ {A : Type} (a : C.Str A), sizes.localSize (code.unit a) ≤ allowance
  bool : ∀ value, sizes.localSize (code.bool value) ≤ allowance
  nat : ∀ value, sizes.localSize (code.nat value) ≤ value + allowance
  nil : ∀ {A : Type} (a : C.Str A), sizes.localSize (code.nil a) ≤ allowance
  cons : ∀ {A : Type} (a : C.Str A), sizes.localSize (code.cons a) ≤ allowance
  select : ∀ {A : Type} (a : C.Str A), sizes.localSize (code.select a) ≤ allowance
  fold : ∀ {A B E : Type} (a : C.Str A) (b : C.Str B) (e : C.Str E)
    {step : A × (B × E) → B}
    (body : Q.Realizer (StepClass.HasProd.prod a (StepClass.HasProd.prod b e)) b step),
    sizes.localSize (code.fold a b e body) ≤ sizes.localSize body + allowance

namespace LocalDescriptionLaws

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {sizes : DescriptionSize Q} {allowance : Nat} (laws : LocalDescriptionLaws sizes allowance)

include laws

theorem compose_bound {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : B → D} {left : Q.Realizer a b f} {right : Q.Realizer b d g}
    {L R : Nat} (hl : sizes.localSize left ≤ L) (hr : sizes.localSize right ≤ R) :
    sizes.localSize (Q.compose left right) ≤ L + R + allowance :=
  (laws.compose left right).trans (Nat.add_le_add_right (Nat.add_le_add hl hr) allowance)

theorem pair_bound {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : A → D} {left : Q.Realizer a b f} {right : Q.Realizer a d g}
    {L R : Nat} (hl : sizes.localSize left ≤ L) (hr : sizes.localSize right ≤ R) :
    sizes.localSize (QP.pair left right) ≤ L + R + allowance :=
  (laws.pair left right).trans (Nat.add_le_add_right (Nat.add_le_add hl hr) allowance)

theorem elim_bound {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → D} {g : B → D} {left : Q.Realizer a d f} {right : Q.Realizer b d g}
    {L R : Nat} (hl : sizes.localSize left ≤ L) (hr : sizes.localSize right ≤ R) :
    sizes.localSize (QS.elim left right) ≤ L + R + allowance :=
  (laws.elim left right).trans (Nat.add_le_add_right (Nat.add_le_add hl hr) allowance)

end LocalDescriptionLaws

end Signatures.Runtime.BackendProgram
