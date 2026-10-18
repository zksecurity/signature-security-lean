import Signatures.Runtime.BackendProgram

/-! Structural refinement of oracle computations. Both sides make exactly the
same adaptive queries and receive the same replies; only their returned values
are related. This stronger-than-distribution relation composes without choosing
a probabilistic oracle interpretation.
-/

namespace Signatures.Runtime.CaliperBackend

open OracleComp OracleSpec

variable {I A B D E : Type} {spec : OracleSpec I}

inductive Synchronizes (relation : A → B → Prop) : OracleComp spec A → OracleComp spec B → Prop where
  | pure {left right} : relation left right → Synchronizes relation (pure left) (pure right)
  | query (position : I) {left : spec.Range position → OracleComp spec A}
      {right : spec.Range position → OracleComp spec B} :
      (∀ answer, Synchronizes relation (left answer) (right answer)) →
      Synchronizes relation (queryBind position left) (queryBind position right)

theorem Synchronizes.mono {relation : A → B → Prop} {stronger : A → B → Prop}
    {left : OracleComp spec A} {right : OracleComp spec B}
    (related : Synchronizes relation left right) (implies : ∀ a b, relation a b → stronger a b) :
    Synchronizes stronger left right := by
  induction related with
  | pure h => exact .pure (implies _ _ h)
  | query position _ ih => exact .query position ih

theorem Synchronizes.bind {relation : A → B → Prop} {result : D → E → Prop}
    {left : OracleComp spec A} {right : OracleComp spec B}
    (related : Synchronizes relation left right)
    (nextLeft : A → OracleComp spec D) (nextRight : B → OracleComp spec E)
    (next : ∀ a b, relation a b → Synchronizes result (nextLeft a) (nextRight b)) :
    Synchronizes result (left >>= nextLeft) (right >>= nextRight) := by
  induction related with
  | pure h => simpa using next _ _ h
  | query position _ ih => exact .query position ih

theorem Synchronizes.map {relation : A → B → Prop} {result : D → E → Prop}
    {left : OracleComp spec A} {right : OracleComp spec B}
    (related : Synchronizes relation left right) (f : A → D) (g : B → E)
    (preserves : ∀ a b, relation a b → result (f a) (g b)) :
    Synchronizes result (f <$> left) (g <$> right) := by
  simpa only [bind_pure_comp] using related.bind (fun a => (Pure.pure (f a) : OracleComp spec D))
    (fun b => (Pure.pure (g b) : OracleComp spec E))
    (fun a b h => Synchronizes.pure (preserves a b h))

/-- Equal observations give literal equality of the adaptive oracle trees. -/
theorem Synchronizes.map_eq {relation : A → B → Prop}
    {left : OracleComp spec A} {right : OracleComp spec B}
    (related : Synchronizes relation left right) (f : A → D) (g : B → D)
    (observations : ∀ a b, relation a b → f a = g b) : f <$> left = g <$> right := by
  induction related with
  | pure h => simp [observations _ _ h]
  | query position _ ih =>
    change queryBind position (fun answer => f <$> _) = queryBind position (fun answer => g <$> _)
    congr 1
    funext answer
    exact ih answer

/-- Every reachable target leaf has a related reachable source leaf. -/
theorem Synchronizes.right_support {relation : A → B → Prop}
    {left : OracleComp spec A} {right : OracleComp spec B}
    (related : Synchronizes relation left right) {value : B} (reachable : value ∈ support right) :
    ∃ source, source ∈ support left ∧ relation source value := by
  induction related with
  | pure h =>
    simp only [support_pure, Set.mem_singleton_iff] at reachable
    subst value
    exact ⟨_, by simp, h⟩
  | query position _ ih =>
    obtain ⟨answer, reachable⟩ := Set.mem_iUnion.mp reachable
    obtain ⟨source, reached, related⟩ := ih answer reachable
    exact ⟨source, Set.mem_iUnion.mpr ⟨answer, reached⟩, related⟩

end Signatures.Runtime.CaliperBackend
