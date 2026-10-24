import Proofs.Runtime.BackendDescriptionLaws
import Proofs.Runtime.BackendCaller

/-! Static overhead of assembling an arbitrary caller. The caller's actual
initialization/head/update descriptions remain explicit. Only generic dispatch
constructors receive the fixed backend's structural allowance, which may depend
on its representation/parameter family. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]

structure DispatchDescriptionLaws (sizes : DescriptionSize Q) (allowance : Nat) : Prop where
  inl : ∀ {A B : Type} (a : C.Str A) (b : C.Str B), sizes.localSize (QS.inl a b) ≤ allowance
  inr : ∀ {A B : Type} (a : C.Str A) (b : C.Str B), sizes.localSize (QS.inr a b) ≤ allowance
  none : ∀ {A B : Type} (a : C.Str A) (b : C.Str B), sizes.localSize (QO.none a b) ≤ allowance
  some : ∀ {A : Type} (a : C.Str A), sizes.localSize (OC.someCode a) ≤ allowance
  getD : ∀ {A : Type} (a : C.Str A), sizes.localSize (OC.getDCode a) ≤ allowance
  distribute : ∀ {A B E : Type} (a : C.Str A) (b : C.Str B) (e : C.Str E),
    sizes.localSize (QD.distribute a b e) ≤ allowance

namespace Caller

variable {I A B S J : Type} {source : OracleSpec I} [DecidableEq I]
  {bd : Boundary C source.toPFunctor A B}
  (R : GeneralCaller.Caller (Q := Q) (bd := bd)) (store : C.Str S)
  {target : OracleSpec J} {iface : Interface (C := C) target}
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dispatchLaws : DispatchDescriptionLaws (Q := Q) sizes allowance)

include laws dispatchLaws

theorem inspect_descriptionSize :
    sizes.localSize (inspectCode R store) ≤ sizes.localSize R.headCode + 6 * allowance := by
  refine (laws.compose_bound
    (laws.pair_bound (laws.compose_bound (laws.fst _ _) (le_refl (sizes.localSize R.headCode))) (laws.identity _))
    (dispatchLaws.distribute _ _ _)).trans ?_
  omega

theorem done_descriptionSize : sizes.localSize (doneCode R store) ≤ 7 * allowance := by
  refine (laws.pair_bound (laws.compose_bound (laws.fst _ _) (dispatchLaws.some _))
    (laws.compose_bound (laws.snd _ _) (laws.snd _ _))).trans ?_
  omega

omit dispatchLaws QO QD OC in
theorem queryArgs_descriptionSize : sizes.localSize (queryArgsCode R store) ≤ 9 * allowance := by
  refine (laws.pair_bound
    (laws.pair_bound (laws.fst _ _) (laws.compose_bound (laws.snd _ _) (laws.snd _ _)))
    (laws.compose_bound (laws.snd _ _) (laws.fst _ _))).trans ?_
  omega

omit dispatchLaws QO QD OC in
theorem resumeArgs_descriptionSize : sizes.localSize (resumeArgsCode R store) ≤ 9 * allowance := by
  refine (laws.pair_bound
    (laws.pair_bound (laws.snd _ _) (laws.compose_bound (laws.fst _ _) (laws.fst _ _)))
    (laws.compose_bound (laws.fst _ _) (laws.snd _ _))).trans ?_
  omega

theorem update_descriptionSize :
    sizes.localSize (updateCode R) ≤ sizes.localSize R.updateCode + 4 * allowance := by
  refine (laws.compose_bound (laws.pair_bound (le_refl (sizes.localSize R.updateCode)) (laws.fst _ _))
    (dispatchLaws.getD _)).trans ?_
  omega

theorem cutoff_descriptionSize : sizes.localSize (cutoffCode R store) ≤ 5 * allowance := by
  refine (laws.pair_bound (dispatchLaws.none _ _) (laws.compose_bound (laws.snd _ _) (laws.snd _ _))).trans ?_
  omega

theorem wiringDescriptionSize_bound : wiringDescriptionSize R store sizes ≤
    sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode + 55 * allowance + 26 := by
  have hi := inspect_descriptionSize R store sizes allowance laws dispatchLaws
  have hd := done_descriptionSize R store sizes allowance laws dispatchLaws
  have hq := queryArgs_descriptionSize R store sizes allowance laws
  have hr := resumeArgs_descriptionSize R store sizes allowance laws
  have hu := update_descriptionSize R sizes allowance laws dispatchLaws
  have hc := cutoff_descriptionSize R store sizes allowance laws dispatchLaws
  have hl := dispatchLaws.inl (result (bd := bd) store) (frame R store)
  have hn := dispatchLaws.inr (result (bd := bd) store) (frame R store)
  dsimp only [wiringDescriptionSize]
  omega

theorem program_descriptionSize_bound
    (handler : Code Q target iface (StepClass.HasProd.prod bd.pos store) (StepClass.HasProd.prod bd.idx store)) (fuel : Nat) :
    (program R store handler fuel).descriptionSize sizes ≤
      sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode +
      handler.descriptionSize sizes + fuel + 55 * allowance + 26 := by
  rw [program_descriptionSize]
  have h := wiringDescriptionSize_bound R store sizes allowance laws dispatchLaws
  omega

end Caller
end Signatures.Runtime.BackendProgram
