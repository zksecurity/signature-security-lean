import Signatures.SynchronizedPS.GeneralAGMFamilyStatement
import Lean.Util.CollectAxioms

/-! Guard the general-backend synchronized PS route: module placement, axioms, no packaged solver
budget or finite period/message/public-key domain in the public records, and one shared solver
class for both weighted schemes. -/

open Lean Meta
open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.WeightedAGM

namespace SignaturesTest.SyncGeneralStatement

run_meta do
  for (name, moduleName) in #[
      (``SynchronizedPS.GeneralAGM.security, `Proofs.SynchronizedPS.GeneralAGM),
      (``SynchronizedPS.GeneralAGM.security_of_hardness, `Proofs.SynchronizedPS.GeneralAGM),
      (``SynchronizedPS.GeneralAGM.agm_security, `Proofs.SynchronizedPS.GeneralAGM),
      (``SynchronizedPS.GeneralAGM.Family.Proofs.security, `Proofs.SynchronizedPS.GeneralAGMFamily),
      (``SynchronizedPS.GeneralAGM.agm_security_asymptotic, `Signatures.SynchronizedPS.GeneralAGMFamilyStatement)] do
    unless (← findModuleOf? name) == some moduleName do
      throwError "{name}: must remain in {moduleName}"

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SyncWrapGeneral.runsWithin, ``SyncWrapGeneral.storedCode, ``SyncWrapGeneral.implements,
      ``SyncWrapGeneral.implementsWithin, ``SyncWrapGeneral.decode_translate_eq_wrap,
      ``SyncWrapGeneral.dlog11Advantage_sample_le,
      ``SynchronizedPS.GeneralAGM.AlgebraicAdversary.reductions_within₁, ``SynchronizedPS.GeneralAGM.AlgebraicAdversary.reductions_within₂,
      ``SynchronizedPS.GeneralAGM.AlgebraicAdversary.good₁_advantage, ``SynchronizedPS.GeneralAGM.AlgebraicAdversary.bad₁_advantage,
      ``SynchronizedPS.GeneralAGM.AlgebraicAdversary.good₂_advantage, ``SynchronizedPS.GeneralAGM.AlgebraicAdversary.bad₂_advantage,
      ``SynchronizedPS.GeneralAGM.security, ``SynchronizedPS.GeneralAGM.security_of_hardness,
      ``SynchronizedPS.GeneralAGM.agm_security, ``SynchronizedPS.GeneralAGM.Family.reductions_nonuniform,
      ``SynchronizedPS.GeneralAGM.Family.Proofs.security, ``SynchronizedPS.GeneralAGM.agm_security_asymptotic] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

-- The records carry the attacker's own interface and allowances. No completed solver budget,
-- hardness assumption or finite period/message/public-key domain is a field or premise.
run_meta do
  for name in #[``SyncWrapGeneral.Parameters.mk, ``SynchronizedPS.GeneralAGM.AlgebraicAdversary.mk,
      ``SynchronizedPS.GeneralAGM.security, ``SynchronizedPS.GeneralAGM.agm_security,
      ``SynchronizedPS.GeneralAGM.agm_security_asymptotic] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Within, ``Bounds, ``GeneralCaller.Budget, ``Model.HardWithin,
            ``NativeSolver.dlogWithin, ``NativeSolver.ExtractionReady, ``NativeHandler.ReservedState,
            ``Model.LazyAGM.WeightedReduction.TranscriptCached] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: supplied reduction budget or internal invariant: {forbidden}"
        forallTelescope type fun _ premise => do
          if premise.isAppOf ``Finite || premise.isAppOf ``Fintype then
            for base in params do
              let decl ← getFVarLocalDecl base
              if #[`K, `M, `G₂].contains decl.userName && (premise.find? (fun e => e == base)).isSome then
                throwError "{name}: finite period/message/public-key domain"

-- The statements display the public game and the derived hardness quantities.
run_meta do
  for (name, visible) in #[
      (``SynchronizedPS.GeneralAGM.agm_security,
        #[``SynchronizedPS.Game.agm, ``SynchronizedPS.GeneralAGM.Parameters.securityBound]),
      (``SynchronizedPS.GeneralAGM.agm_security_asymptotic,
        #[``SynchronizedPS.Game.agm, ``SynchronizedPS.GeneralAGM.Family.dlogHardness, ``SynchronizedPS.GeneralAGM.Family.PolynomialResources,
          ``Model.PairingCurve.order])] do
    let type := (← getConstInfo name).type
    for symbol in visible do
      unless (type.find? (fun e => e.isConstOf symbol)).isSome do
        throwError "{name}: must display {symbol}"
  for name in #[``SynchronizedPS.GeneralAGM.Parameters.securityBound, ``SynchronizedPS.GeneralAGM.Parameters.dlogBound] do
    unless (← getConstInfo name).value?.isSome do
      throwError "{name} must be a transparent definition"

universe v w x

section
variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]
  {generator : G₁} {keyGenerator : G₂}
  (P : SynchronizedPS.GeneralAGM.Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (K := K) (M := M)
    generator keyGenerator)

-- Both weighted schemes' pipelines share the solver class and its hardness quantity.
example (time : Nat) : (P.toGeneral true).dlogBound time = P.dlogBound time := rfl

-- The wrapper's budgets are the attacker's plus the derived wrapper costs, in the pipeline's own record.
example : (P.toGeneral false).execution = P.execution := rfl
example : (P.toGeneral false).callerCodeLimit = P.callerCodeLimit := rfl
example : (P.toGeneral false).queries = ⟨P.innerQueries.random, P.innerQueries.hash + P.innerQueries.sign + 1, P.innerQueries.sign⟩ := rfl

-- The attacker's source is the public game's algebraic adversary, viewed from the key's components.
example (A : SynchronizedPS.GeneralAGM.AlgebraicAdversary P) :
    A.view = SynchronizedPS.Proofs.view A.source generator := rfl
end

end SignaturesTest.SyncGeneralStatement
