import Proofs.Runtime.Program

/-! Structural refinement between oracle trees with different result types.
Every query and possible reply is matched exactly. This supports heap-root vs
semantic-value proofs without an executable decoder or a probability model. -/

namespace Signatures.Runtime

open OracleComp
open scoped OracleSpec.PrimitiveQuery

variable {I : Type} {spec : OracleSpec I} {A B C D E : Type}

inductive QueryTreeRel (R : A → B → Prop) : OracleComp spec A → OracleComp spec B → Prop
  | pure {a b} : R a b → QueryTreeRel R (pure a) (pure b)
  | queryBind (q : spec.Domain) (left : spec.Range q → OracleComp spec A)
      (right : spec.Range q → OracleComp spec B) :
      (∀ reply, QueryTreeRel R (left reply) (right reply)) →
      QueryTreeRel R (query q >>= left) (query q >>= right)

namespace QueryTreeRel

variable {R : A → B → Prop} {left : OracleComp spec A} {right : OracleComp spec B}

theorem refl (code : OracleComp spec A) : QueryTreeRel Eq code code := by
  induction code using OracleComp.inductionOn with
  | pure x => exact .pure rfl
  | query_bind q next ih => exact .queryBind q next next ih

theorem mono (h : QueryTreeRel R left right) {S : A → B → Prop}
    (hs : ∀ a b, R a b → S a b) : QueryTreeRel S left right := by
  induction h with
  | pure hr => exact .pure (hs _ _ hr)
  | queryBind q f g _ ih => exact .queryBind q f g ih

theorem symm (h : QueryTreeRel R left right) : QueryTreeRel (fun b a => R a b) right left := by
  induction h with
  | pure hr => exact .pure hr
  | queryBind q f g _ ih => exact .queryBind q g f ih

theorem bind (h : QueryTreeRel R left right) {S : C → D → Prop}
    (f : A → OracleComp spec C) (g : B → OracleComp spec D)
    (hfg : ∀ a b, R a b → QueryTreeRel S (f a) (g b)) :
    QueryTreeRel S (left >>= f) (right >>= g) := by
  induction h with
  | pure hr => simpa only [pure_bind] using hfg _ _ hr
  | queryBind q l r _ ih =>
    simpa only [bind_assoc] using QueryTreeRel.queryBind q (fun x => l x >>= f) (fun x => r x >>= g) ih

theorem map (h : QueryTreeRel R left right) {S : C → D → Prop}
    (f : A → C) (g : B → D) (hfg : ∀ a b, R a b → S (f a) (g b)) :
    QueryTreeRel S (f <$> left) (g <$> right) := by
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using h.bind (fun a => Pure.pure (f a)) (fun b => Pure.pure (g b))
    (fun a b hab => .pure (hfg a b hab))

/-- Any observation that agrees on related leaves gives equal query trees. -/
theorem map_eq (h : QueryTreeRel R left right) (f : A → E) (g : B → E)
    (hfg : ∀ a b, R a b → f a = g b) : f <$> left = g <$> right := by
  induction h with
  | pure hr => simp only [map_pure, hfg _ _ hr]
  | queryBind q l r _ ih =>
    simp only [map_bind]
    exact congrArg (fun k : spec.Range q → OracleComp spec E =>
      (query q : OracleComp spec _) >>= k) (funext ih)

theorem support_left (h : QueryTreeRel R left right) (a : A) (ha : a ∈ support left) :
    ∃ b ∈ support right, R a b := by
  induction h with
  | pure hr =>
    simp only [support_pure, Set.mem_singleton_iff] at ha
    subst a
    exact ⟨_, by simp, hr⟩
  | queryBind q l r _ ih =>
    simp only [mem_support_bind_iff] at ha
    obtain ⟨reply, hreply, ha⟩ := ha
    obtain ⟨b, hb, hab⟩ := ih reply ha
    exact ⟨b, by simpa only [mem_support_bind_iff] using ⟨reply, hreply, hb⟩, hab⟩

theorem support_right (h : QueryTreeRel R left right) (b : B) (hb : b ∈ support right) :
    ∃ a ∈ support left, R a b := h.symm.support_left b hb

theorem with_support (h : QueryTreeRel R left right) :
    QueryTreeRel (fun a b => a ∈ support left ∧ b ∈ support right ∧ R a b) left right := by
  induction h with
  | pure hr => exact .pure ⟨by simp, by simp, hr⟩
  | queryBind q l r _ ih =>
    apply QueryTreeRel.queryBind q l r
    intro reply
    apply (ih reply).mono
    intro a b hab
    refine ⟨?_, ?_, hab.2.2⟩
    · simp only [mem_support_bind_iff]
      exact ⟨reply, mem_support_query q reply, hab.1⟩
    · simp only [mem_support_bind_iff]
      exact ⟨reply, mem_support_query q reply, hab.2.1⟩

/-- Prefix budgets and trace checks are only needed at reachable paired leaves. -/
theorem bind_support (h : QueryTreeRel R left right) {S : C → D → Prop}
    (f : A → OracleComp spec C) (g : B → OracleComp spec D)
    (hfg : ∀ a ∈ support left, ∀ b ∈ support right, R a b → QueryTreeRel S (f a) (g b)) :
    QueryTreeRel S (left >>= f) (right >>= g) :=
  h.with_support.bind f g (fun a b hab => hfg a hab.1 b hab.2.1 hab.2.2)

end QueryTreeRel

end Signatures.Runtime
