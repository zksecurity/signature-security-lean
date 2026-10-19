import Signatures.Runtime.Caliper.Synchronizes

/-! Equality of observed free computations determines their common adaptive
query tree. This is literal equality before probabilistic interpretation, not
merely equality of output distributions. -/

namespace Signatures.Runtime.CaliperBackend
open OracleComp OracleSpec

variable {I A B D : Type} {spec : OracleSpec I}

theorem Synchronizes.symm {relation : A → B → Prop}
    {left : OracleComp spec A} {right : OracleComp spec B}
    (related : Synchronizes relation left right) :
    Synchronizes (fun b a => relation a b) right left := by
  induction related with
  | pure equal => exact .pure equal
  | query position _ ih => exact .query position ih

theorem Synchronizes.left_support {relation : A → B → Prop}
    {left : OracleComp spec A} {right : OracleComp spec B}
    (related : Synchronizes relation left right) {value : A} (reached : value ∈ support left) :
    ∃ answer, answer ∈ support right ∧ relation value answer := related.symm.right_support reached

/-- Recover joint leaf synchronization from an equality of observed query
trees. Neither observation has to be injective. -/
theorem Synchronizes.of_map_eq (f : A → D) (g : B → D)
    {left : OracleComp spec A} {right : OracleComp spec B}
    (equal : f <$> left = g <$> right) :
    Synchronizes (fun a b => f a = g b) left right := by
  change PFunctor.FreeM.map f left = PFunctor.FreeM.map g right at equal
  induction left generalizing right with
  | pure a =>
    cases right with
    | pure b => exact .pure ((PFunctor.FreeM.pure_inj _ _).mp equal)
    | queryBind position next => cases equal
  | queryBind position next ih =>
    cases right with
    | pure b => cases equal
    | queryBind other after =>
      simp only [PFunctor.FreeM.map_liftBind] at equal
      obtain ⟨rfl, continuations⟩ := (PFunctor.FreeM.liftBind_inj _ _ _ _).mp equal
      exact .query position (fun answer => ih answer (congrFun continuations answer))

theorem Synchronizes.iff_map_eq (f : A → D) (g : B → D)
    (left : OracleComp spec A) (right : OracleComp spec B) :
    Synchronizes (fun a b => f a = g b) left right ↔ f <$> left = g <$> right :=
  ⟨fun related => related.map_eq f g (fun _ _ equal => equal), Synchronizes.of_map_eq f g⟩

end Signatures.Runtime.CaliperBackend
