import Signatures.Schnorr.GeneralAGMFamilyStatement
import Lean.Util.CollectAxioms

/-! Guard the asymptotic theorem's resources, fixed-backend hardness and axiom
scope. Polynomial code/time must follow from component contracts; unbounded
message types and large numerical random ranges must remain supported. -/

open Lean Meta PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.SchnorrAGM.Native
open Signatures.Runtime.SchnorrAGM.Native.Solver.Family

namespace SignaturesTest.SchnorrAGMFamilies

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Flatten.flattenTime_polynomial, ``Read.readTime_polynomial,
      ``Hash.hashTime_polynomial, ``Extraction.extractionTime_polynomial,
      ``Handler.timeBudget_polynomial, ``Solver.terminalTime_polynomial,
      ``Solver.programTime_polynomial, ``Solver.programDescription_polynomial,
      ``Schnorr.GeneralAGM.Family.PolynomialResources.totalQueries,
      ``Schnorr.GeneralAGM.Family.PolynomialResources.executionQueries,
      ``Schnorr.GeneralAGM.Family.PolynomialResources.solverTime,
      ``Schnorr.GeneralAGM.Family.PolynomialResources.solverCode,
      ``Schnorr.GeneralAGM.Family.reduction_nonuniform,
      ``Schnorr.GeneralAGM.Family.Proofs.security,
      ``Schnorr.GeneralAGM.Family.security_asymptotic] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

run_meta do
  for name in #[``Handler.PolynomialTimes.mk,
      ``Schnorr.GeneralAGM.Family.PolynomialResources.mk,
      ``Schnorr.GeneralAGM.Family.reduction_nonuniform,
      ``Schnorr.GeneralAGM.Family.security_asymptotic] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Within, ``NonuniformWithin, ``Configuration.within,
            ``Configuration.nonuniformWithin, ``Solver.dlogWithin, ``dlogNonuniformWithin,
            ``Bounds, ``GeneralCaller.Budget, `Signatures.Runtime.Schnorr.SourceCertificate,
            ``Solver.programTime, ``Solver.programDescription,
            ``Schnorr.GeneralAGM.Parameters.solverTime, ``Schnorr.GeneralAGM.Parameters.solverCode,
            ``Schnorr.GeneralAGM.Parameters.arityCap] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: completed-solver budget, restricted caller or polynomial raw arity premise: {forbidden}"
        forallTelescope type fun _ premise => do
          if premise.isAppOf ``Finite || premise.isAppOf ``Fintype then
            for base in params do
              let declaration ← getFVarLocalDecl base
              if #[`M, `G].contains declaration.userName &&
                  (premise.find? (fun e => e == base)).isSome then
                throwError "{name}: explicit finite message/group domain requirement"

run_meta do
  let name := ``Schnorr.GeneralAGM.Family.security_asymptotic
  forallTelescope (← getConstInfo name).type fun params conclusion => do
    for required in #[`parameters, `config, `fixed, `resources, `adversary, `hardness, `fieldGrowth] do
      unless (← params.anyM fun p => return (← getFVarLocalDecl p).userName == required) do
        throwError "{name}: missing family condition {required}"
    for param in params do
      let declaration ← getFVarLocalDecl param
      let type ← inferType param
      if #[`F, `G, `M].contains declaration.userName then
        unless type.isForall && type.bindingDomain!.isConstOf ``Nat && type.bindingBody!.isSort do
          throwError "{name}: {declaration.userName} must vary with the security parameter"
      if declaration.userName == `hardness then
        unless type.isAppOf ``dlogNonuniformHardness do
          throwError "{name}: hardness must cover the fixed backend's native solver families"
      if declaration.userName == `fixed then
        unless (type.find? (fun e => e.isConstOf ``Schnorr.GeneralAGM.Parameters.configuration)).isSome do
          throwError "{name}: configuration must remain fixed across parameters"
    unless conclusion.isAppOf ``negligible &&
        (conclusion.find? (fun e => e.isConstOf ``Schnorr.AGM.game)).isSome do
      throwError "{name}: must conclude negligible success in the actual Schnorr AGM game"
  unless (← findModuleOf? name) == some `Signatures.Schnorr.GeneralAGMFamilyStatement do
    throwError "Family statement must stay in its statement file"
  unless (← findModuleOf? ``Schnorr.GeneralAGM.Family.Proofs.security) == some `Signatures.Schnorr.Proofs.GeneralAGMFamily do
    throwError "Family proof must stay in its separate proof file"

private def linearTimes (n : Nat) : Handler.Times := ⟨n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n⟩

private theorem linearTimes_polynomial : Handler.PolynomialTimes linearTimes := by
  constructor <;> exact PolynomiallyBounded.input

-- Zero query allowances still charge setup and terminal handling. The actual
-- numerical formula remains polynomial, without dividing by a query count.
example (overhead : Nat → Nat → Nat) (h : PolynomialOverhead overhead) :
    PolynomiallyBounded (fun n => Solver.programTime (overhead n)
      ⟨n, 0, 0, n, n⟩ n n n n 0 2 0 n n n n 0 n n n (linearTimes n)) := by
  exact Solver.programTime_polynomial overhead (fun n => ⟨n, 0, 0, n, n⟩)
    id id id id (fun _ => 0) (fun _ => 2) (fun _ => 0) id id id id (fun _ => 0)
    id id id linearTimes h PolynomiallyBounded.input (PolynomiallyBounded.const 0)
    PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input
    (PolynomiallyBounded.const 0) (PolynomiallyBounded.const 2) (PolynomiallyBounded.const 0)
    PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input
    (PolynomiallyBounded.const 0) PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input
    linearTimes_polynomial

example : 0 < Solver.programTime (fun _ => 1) ⟨0, 0, 0, 0, 0⟩
    0 0 0 0 0 2 0 0 0 0 0 0 0 0 0 (linearTimes 0) := by decide

end SignaturesTest.SchnorrAGMFamilies
