import Signatures.BLS.Statement
import Signatures.Schnorr.Statement
import Lean.Util.CollectAxioms

/-! Polynomial Caliper families derive full reduction resources from original
components. Guard the actual public route, its assumptions, and proof axioms. -/
namespace SignaturesTest.CaliperFamilies
open Lean Meta Signatures.Runtime Signatures.Runtime.CaliperBackend

-- Arithmetic closure permits arbitrary branch conditions and subtraction's
-- right operand; neither can increase the bound beyond the proved operands.
example (f g arbitrary : Nat → Nat) (condition : Nat → Prop) [∀ n, Decidable (condition n)]
    (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n =>
      max (f n * (g n + 3)) (if condition n then f n else g n) + (f n - arbitrary n)) := by
  caliper_polynomial

-- Unknown local costs do not become polynomial by unfolding a wrapper.
example (_unknownCost : Nat → Nat) : True := by
  fail_if_success
    have : PolynomiallyBounded _unknownCost := by caliper_polynomial
  trivial

-- Inferred intermediate bounds can retain assigned type metavariables.
-- The tactic must use those proofs after the original component facts leave scope.
example (f g : Nat → Nat) (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => (f n + g n) * (f n + g n)) := by
  have combined := hf.add hg
  clear hf hg
  caliper_polynomial

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Interactive.NonuniformWithin.of_pointwise, ``dlogNonuniformWithin.of_pointwise,
      ``BLS.CaliperAGM.Family.PolynomialResources.goodTime,
      ``BLS.CaliperAGM.Family.PolynomialResources.badTime,
      ``BLS.CaliperAGM.Family.PolynomialResources.solverCode,
      ``BLS.CaliperAGM.Family.PolynomialResources.solverMemory,
      ``BLS.CaliperAGM.Family.reductions_nonuniform, ``BLS.agm_security_asymptotic,
      ``cyclicDLogNonuniformWithin.of_pointwise,
      ``Schnorr.CaliperAGM.Family.PolynomialResources.solverTime,
      ``Schnorr.CaliperAGM.Family.PolynomialResources.solverCode,
      ``Schnorr.CaliperAGM.Family.PolynomialResources.solverMemory,
      ``Schnorr.CaliperAGM.Family.reduction_nonuniform, ``Schnorr.agm_security_asymptotic] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

-- Polynomiality of the completed reductions is a conclusion, not a field in
-- the component record. Nor do we constrain the cardinality of the sampling range.
run_meta do
  let type := (← getConstInfo ``BLS.CaliperAGM.Family.PolynomialResources.mk).type
  for forbidden in #[``BLS.CaliperAGM.Parameters.goodTime, ``BLS.CaliperAGM.Parameters.badTime,
      ``BLS.CaliperAGM.Parameters.goodWords, ``BLS.CaliperAGM.Parameters.badWords,
      ``BLS.CaliperAGM.Parameters.solverCode, ``BLS.CaliperAGM.Parameters.solverMemory,
      ``BLSFull.Layouts.randomBound, ``Fintype.card, ``Interactive.Within,
      ``Interactive.NonuniformWithin, ``dlogNonuniformWithin, ``dlogNonuniformHardness] do
    if (type.find? (fun e => e.isConstOf forbidden)).isSome then
      throwError "polynomial component record contains a completed-solver or domain-size premise: {forbidden}"
  for required in #[``BLS.CaliperAGM.Parameters.wordBits, ``BLSFull.Layouts.state,
      ``BLS.CaliperAGM.Parameters.callerLimits, ``BLS.CaliperAGM.Parameters.primitiveBounds] do
    unless (type.find? (fun e => e.isConstOf required)).isSome do
      throwError "polynomial component record is missing {required}"

run_meta do
  unless (← findModuleOf? ``BLS.agm_security_asymptotic) == some `Signatures.BLS.CaliperAGMFamilyStatement do
    throwError "keep the public Caliper family statement in its statement file"
  unless (← findModuleOf? ``BLS.CaliperAGM.Family.Proofs.security) == some `Proofs.BLS.CaliperAGMFamily do
    throwError "keep the family proof in its separate proof file"
  let info ← getConstInfo ``BLS.CaliperAGM.Family.Proofs.security
  let proof := (info.value? true).getD info.type
  unless (proof.find? (fun e => e.isConstOf ``BLS.CaliperAGM.Family.reductions_nonuniform)).isSome do
    throwError "public family proof must use the constructed Caliper reductions"
  for forbidden in #[`BLS.GeneralAGM.Family.reductions_nonuniform,
      `Signatures.Runtime.BackendProgram.NonuniformWithin] do
    if (proof.find? (fun e => e.isConstOf forbidden)).isSome then
      throwError "old abstract backend in Caliper family proof: {forbidden}"
  let definition := (← getConstInfo ``Interactive.NonuniformWithin).value?.get!
  unless (definition.find? (fun e => e.isConstOf ``Interactive.Within)).isSome do
    throwError "family class must retain actual Caliper implementation certificates"
  unless (definition.find? (fun e => e.isConstOf ``PolynomiallyBounded)).isSome do
    throwError "family class must require one polynomial across parameters"

run_meta do
  let type := (← getConstInfo ``Schnorr.CaliperAGM.Family.PolynomialResources.mk).type
  for forbidden in #[``Schnorr.CaliperAGM.Parameters.solverTime, ``Schnorr.CaliperAGM.Parameters.solverCode,
      ``Schnorr.CaliperAGM.Parameters.solverMemory,
      ``Fintype.card, ``Interactive.Within, ``Interactive.NonuniformWithin,
      ``cyclicDLogNonuniformWithin, ``cyclicDLogNonuniformHardness] do
    if (type.find? (fun e => e.isConstOf forbidden)).isSome then
      throwError "Schnorr polynomial assumptions contain a solver or domain-size bound: {forbidden}"
  -- The arity also indexes layout types, so inspect the bounded function itself.
  forallTelescope type fun params _ => do
    for param in params do
      let premise ← inferType param
      if premise.isAppOf ``PolynomiallyBounded then
        lambdaTelescope premise.getAppArgs[0]! fun _ body => do
          if body.getAppFn.isConstOf ``Schnorr.CaliperAGM.Parameters.randomBound then
            throwError "numerical sampling arity must not be required polynomial"
  for required in #[``Schnorr.CaliperAGM.Parameters.wordBits, ``Schnorr.CaliperAGM.Parameters.callerLimits,
      ``Schnorr.CaliperAGM.Parameters.primitiveBounds,
      ``Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerExtraction.Layouts.state] do
    unless (type.find? (fun e => e.isConstOf required)).isSome do
      throwError "Schnorr polynomial components omit {required}"
  unless (← findModuleOf? ``Schnorr.agm_security_asymptotic) == some `Signatures.Schnorr.CaliperAGMFamilyStatement do
    throwError "keep the Schnorr family statement separate"
  unless (← findModuleOf? ``Schnorr.CaliperAGM.Family.Proofs.security) == some `Proofs.Schnorr.CaliperAGMFamily do
    throwError "keep the Schnorr family proof separate"
  let info ← getConstInfo ``Schnorr.CaliperAGM.Family.Proofs.security
  let proof := (info.value? true).getD info.type
  unless (proof.find? (fun e => e.isConstOf ``Schnorr.CaliperAGM.Family.reduction_nonuniform)).isSome do
    throwError "Schnorr family security must use the actual polynomial Caliper reduction"
  for forbidden in #[`Schnorr.GeneralAGM.Family.reduction_nonuniform, `Signatures.Runtime.BackendProgram.NonuniformWithin] do
    if (proof.find? (fun e => e.isConstOf forbidden)).isSome then
      throwError "old abstract backend in Schnorr family proof: {forbidden}"

open OracleComp in
example (curve : Model.PairingCurve) [model : BLS.AGMSecurityModel curve]
    (queries : Nat → BLS.QueryAllowance)
    (adversary : ∀ n, BLS.AlgebraicAdversary curve n (queries n))
    (resources : BLS.CaliperAGM.Family.PolynomialResources (fun n => model.parameters n (queries n)))
    (hardness : BLS.CaliperAGM.Family.dlogHardness (fun n => model.parameters n (queries n)))
    (fieldGrowth : negligible (fun n => 1 / (curve.order n : ENNReal))) :
    negligible (fun n => 𝒟[BLS.Game.agm curve n (adversary n).source] {true}) :=
  BLS.agm_security_asymptotic curve queries adversary resources hardness fieldGrowth

open OracleComp in
example (curve : Model.CyclicCurve) [model : Schnorr.AGMSecurityModel curve]
    (queries : Nat → Schnorr.QueryAllowance)
    (adversary : ∀ n, Schnorr.AlgebraicAdversary curve n (queries n))
    (resources : Schnorr.CaliperAGM.Family.PolynomialResources (fun n => model.parameters n (queries n)))
    (hardness : Schnorr.CaliperAGM.Family.dlogHardness (fun n => model.parameters n (queries n)))
    (fieldGrowth : negligible (fun n => (curve.order n : ENNReal)⁻¹)) :
    negligible (fun n => 𝒟[Schnorr.Game.agm curve n (adversary n).source] {true}) :=
  Schnorr.agm_security_asymptotic curve queries adversary resources hardness fieldGrowth

end SignaturesTest.CaliperFamilies
