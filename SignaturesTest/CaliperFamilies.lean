import Signatures.BLS.Statement
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

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Interactive.NonuniformWithin.of_pointwise, ``dlogNonuniformWithin.of_pointwise,
      ``BLS.CaliperAGM.Family.PolynomialResources.goodTime,
      ``BLS.CaliperAGM.Family.PolynomialResources.badTime,
      ``BLS.CaliperAGM.Family.PolynomialResources.solverCode,
      ``BLS.CaliperAGM.Family.PolynomialResources.solverMemory,
      ``BLS.CaliperAGM.Family.reductions_nonuniform, ``BLS.agm_security_asymptotic] do
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
  unless (← findModuleOf? ``BLS.CaliperAGM.Family.Proofs.security) == some `Signatures.BLS.Proofs.CaliperAGMFamily do
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

open OracleComp in
example (curve : Model.PairingCurve) [model : BLS.AGMSecurityModel curve]
    (queries : Nat → BLS.QueryAllowance)
    (adversary : ∀ n, BLS.AlgebraicAdversary curve n (queries n))
    (resources : BLS.CaliperAGM.Family.PolynomialResources (fun n => model.parameters n (queries n)))
    (hardness : BLS.CaliperAGM.Family.dlogHardness (fun n => model.parameters n (queries n)))
    (fieldGrowth : negligible (fun n => 1 / (curve.order n : ENNReal))) :
    negligible (fun n => 𝒟[BLS.Game.agm curve n (adversary n).source] {true}) :=
  BLS.agm_security_asymptotic curve queries adversary resources hardness fieldGrowth

end SignaturesTest.CaliperFamilies
