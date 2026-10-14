import Signatures.Runtime.BackendLanguageBudget

/-! Bounds for native data adapters and sum dispatch with a retained store.
Every copy, local invocation, sequence edge, and branch selection is charged
using encoded widths. These rules price the constructed code, not a semantic
replacement or an opaque complete handler. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {I : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
  {header : Nat} (sizes : SizeLaws Q header) {overhead : Nat → Nat}
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : I) → spec.Range i → Nat) (routing : RoutingCostLaws control overhead)

include mono routing

omit [C.HasOption] in
theorem firstAtomic_bound_of_width {A B S : Type} {a : C.Str A} {b : C.Str B}
    (store : C.Str S) {f : A → B} (adapter : Q.Realizer a b f)
    (pre : A → Prop) (post : B → Prop) (keep : S → Prop) (width time : Nat)
    (hi : ∀ input, pre input → Q.size a input ≤ width)
    (hs : ∀ saved, keep saved → Q.size store saved ≤ width)
    (hl : ∀ input, pre input → post (f input) ∧ Q.size b (f input) ≤ width ∧ Q.cost adapter input ≤ time) :
    Bounds control queryCost (.first store (.atomic (iface := iface) adapter))
      (fun p => pre p.1 ∧ keep p.2) (fun p => post p.1 ∧ keep p.2)
      (time + 2 * overhead (32 * width)) := by
  intro input hp z hz
  simp only [Code.run, retainRun, map_pure, support_pure, Set.mem_singleton_iff] at hz
  subst z
  obtain ⟨hout, hw, ht⟩ := hl input.1 hp.1
  have hi' := hi input.1 hp.1
  have hs' := hs input.2 hp.2
  have hc := routing.localCall (Q.size a input.1) (Q.size b (f input.1))
  have hr := routing.retain (Q.size store input.2) (Q.size b (f input.1))
  have h1 := mono (show Q.size a input.1 + Q.size b (f input.1) ≤ 32 * width by omega)
  have h2 := mono (show Q.size store input.2 + Q.size b (f input.1) ≤ 32 * width by omega)
  exact ⟨⟨hout, hp.2⟩, by dsimp; omega⟩

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  (dispatch : DispatchCostLaws (Q := Q) overhead)

include sizes dispatch

omit [Q.HasCategory] QP in
theorem branchStore_bound_of_width {A B D S : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    (store : C.Str S)
    (left : Code Q spec iface (StepClass.HasProd.prod a store) d)
    (right : Code Q spec iface (StepClass.HasProd.prod b store) d)
    (preLeft : A × S → Prop) (preRight : B × S → Prop) (post : D → Prop)
    (width leftTime rightTime : Nat) (hh : header ≤ width)
    (hlSize : ∀ p, preLeft p → Q.size a p.1 ≤ width ∧ Q.size store p.2 ≤ width)
    (hrSize : ∀ p, preRight p → Q.size b p.1 ≤ width ∧ Q.size store p.2 ≤ width)
    (hl : Bounds control queryCost left preLeft post leftTime)
    (hr : Bounds control queryCost right preRight post rightTime) :
    Bounds control queryCost (.seq (.atomic (QD.distribute a b store)) (.branch left right))
      (fun p => Sum.elim (fun x => preLeft (x, p.2)) (fun y => preRight (y, p.2)) p.1)
      post (max leftTime rightTime + 4 * overhead (32 * width)) := by
  let pre := fun p : (A ⊕ B) × S =>
    Sum.elim (fun x => preLeft (x, p.2)) (fun y => preRight (y, p.2)) p.1
  let middle := Sum.elim preLeft preRight
  let split := fun p : (A ⊕ B) × S =>
    Sum.elim (fun x => Sum.inl (x, p.2)) (fun y => Sum.inr (y, p.2)) p.1
  have hsplit : ∀ p, pre p → middle (split p) := by
    rintro ⟨x, saved⟩ hp
    cases x <;> exact hp
  have hin : ∀ p, pre p → Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum a b) store) p ≤ 4 * width := by
    rintro ⟨x, saved⟩ hp
    have hprod := sizes.prod_le (StepClass.HasSum.sum a b) store (x, saved)
    have hsum := sizes.sum_le a b x
    cases x with
    | inl value =>
        obtain ⟨hv, hs⟩ := hlSize (value, saved) hp
        dsimp at hprod hsum hv hs
        omega
    | inr value =>
        obtain ⟨hv, hs⟩ := hrSize (value, saved) hp
        dsimp at hprod hsum hv hs
        omega
  have hmid : ∀ p, middle p → Q.size
      (StepClass.HasSum.sum (StepClass.HasProd.prod a store) (StepClass.HasProd.prod b store)) p ≤ 4 * width := by
    intro p hp
    have hsum := sizes.sum_le (StepClass.HasProd.prod a store) (StepClass.HasProd.prod b store) p
    cases p with
    | inl value =>
        obtain ⟨hv, hs⟩ := hlSize value hp
        have hprod := sizes.prod_le a store value
        dsimp at hsum
        omega
    | inr value =>
        obtain ⟨hv, hs⟩ := hrSize value hp
        have hprod := sizes.prod_le b store value
        dsimp at hsum
        omega
  have hd : Bounds control queryCost (.atomic (iface := iface) (QD.distribute a b store))
      pre middle (2 * overhead (32 * width)) := by
    apply Bounds.atomic
    intro input hp
    have ho := hsplit input hp
    have hi := hin input hp
    have hm := hmid (split input) ho
    have hc := dispatch.distribute a b store input
    have hf := routing.localCall
      (Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum a b) store) input)
      (Q.size (StepClass.HasSum.sum (StepClass.HasProd.prod a store) (StepClass.HasProd.prod b store)) (split input))
    have hn := mono (show Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum a b) store) input +
        Q.size (StepClass.HasSum.sum (StepClass.HasProd.prod a store) (StepClass.HasProd.prod b store)) (split input) ≤
          32 * width by omega)
    exact ⟨ho, by dsimp only [split] at *; omega⟩
  have hb := Bounds.branch control queryCost left right preLeft preRight post leftTime rightTime
    (overhead (32 * width)) hl hr (by
      intro input hp
      exact (routing.branch _).trans (mono (by have := hmid input hp; omega)))
  have hj : ∀ input, pre input → ∀ value, middle value →
      control.sequence (Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum a b) store) input)
        (Q.size (StepClass.HasSum.sum (StepClass.HasProd.prod a store) (StepClass.HasProd.prod b store)) value) ≤
          overhead (32 * width) := by
    intro input hi value hv
    exact (routing.sequence _ _).trans (mono (by have := hin input hi; have := hmid value hv; omega))
  have h := Bounds.seq control queryCost _ _ pre middle post _ _ _ hd hb hj
  intro input hp z hz
  obtain ⟨hout, ht⟩ := h input hp z hz
  exact ⟨hout, by omega⟩

end Signatures.Runtime.BackendProgram
