import Signatures.OOPS.GeneralAGMFamilyStatement
import Signatures.Proximity.GeneralAGMFamilyStatement
import Lean.Util.CollectAxioms

/-! Guard varying degrees/dimensions, actual solver resource closure, one fixed
backend and the original Proximity collision loss in the family endpoints. -/

open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.WeightedAGM
open PFunctor

namespace SignaturesTest.WeightedFamilies

-- The common closure theorem even permits changing which weighted scheme is
-- encoded. Numerical dimensions grow; no polynomial field cardinality is used.
private def varyingIndex (n : Nat) : Index :=
  if n % 2 = 0 then .oops n else .proximity (n * n)

private theorem varyingIndex_bound : PolynomiallyBounded (fun n => (varyingIndex n).bound) := by
  apply (PolynomiallyBounded.input.add (PolynomiallyBounded.input.mul PolynomiallyBounded.input)).of_le
  intro n
  unfold varyingIndex
  split <;> simp only [Index.bound, id_eq] <;> omega

private def linear (n : Nat) : Nat := n + 1
private theorem linear_bound : PolynomiallyBounded linear :=
  PolynomiallyBounded.input.add (PolynomiallyBounded.const 1)

private def overhead (n size : Nat) : Nat := n + size + 1
private theorem overhead_bound : PolynomialOverhead overhead :=
  ⟨.add .input (.const 1), fun _ _ => le_rfl⟩

private def caller (n : Nat) : ExecutionCost := ⟨n + 1, n + 1, n + 1, n + 1, n + 1⟩

example : PolynomiallyBounded (fun n => NativeSolver.goodProgramTime (varyingIndex n)
    (overhead n) (caller n) (linear n) (linear n) (linear n) (linear n) (linear n) (linear n)
    (linear n) (linear n) (linear n) (linear n) (linear n) (linear n) (linear n) (linear n) (linear n)) :=
  NativeSolver.goodProgramTime_polynomial varyingIndex overhead caller
    linear linear linear linear linear linear linear linear linear linear linear linear linear linear linear
    varyingIndex_bound overhead_bound linear_bound linear_bound
    linear_bound linear_bound linear_bound linear_bound linear_bound linear_bound linear_bound linear_bound
    linear_bound linear_bound linear_bound linear_bound linear_bound linear_bound linear_bound

example : PolynomiallyBounded (fun n => NativeSolver.badProgramTime (varyingIndex n)
    (overhead n) (caller n) (linear n) (linear n) (linear n) (linear n) (linear n) (linear n)
    (linear n) (linear n) (linear n) (linear n) (linear n) (linear n) (linear n) (linear n) (linear n)) :=
  NativeSolver.badProgramTime_polynomial varyingIndex overhead caller
    linear linear linear linear linear linear linear linear linear linear linear linear linear linear linear
    varyingIndex_bound overhead_bound linear_bound linear_bound
    linear_bound linear_bound linear_bound linear_bound linear_bound linear_bound linear_bound linear_bound
    linear_bound linear_bound linear_bound linear_bound linear_bound linear_bound linear_bound

open Lean Meta

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Index.termsTime_polynomial, ``Index.coefficientTime_polynomial,
      ``NativeSolver.goodProgramTime_polynomial, ``NativeSolver.badProgramTime_polynomial,
      ``NativeSolver.programDescription_polynomial,
      ``General.Family.PolynomialResources.goodTime, ``General.Family.PolynomialResources.badTime,
      ``General.Family.PolynomialResources.solverCode, ``General.Family.solver_nonuniform,
      ``General.Family.reductions_nonuniform,
      ``OOPS.GeneralAGM.Family.reductions_nonuniform, ``Proximity.GeneralAGM.Family.reductions_nonuniform,
      ``OOPS.GeneralAGM.Family.security_asymptotic,
      ``Proximity.GeneralAGM.Family.security_asymptotic, ``Proximity.GeneralAGM.Family.security_up_to_collision] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

-- Inspect the resource constructor: no packaged completed-solver efficiency.
run_meta do
  forallTelescope (← getConstInfo ``General.Family.PolynomialResources.mk).type fun params _ => do
    let mut fields : Array Name := #[]
    for param in params do
      let decl ← getFVarLocalDecl param
      fields := fields.push decl.userName
      let type ← inferType param
      for forbidden in #[``General.Parameters.goodTime, ``General.Parameters.badTime,
          ``General.Parameters.solverCode, ``NativeSolver.goodProgramTime, ``NativeSolver.badProgramTime,
          ``NativeSolver.programDescription, ``Within, ``NonuniformWithin,
          `Signatures.Runtime.AGM.SourceCertificate] do
        if (type.find? (fun e => e.isConstOf forbidden)).isSome then
          throwError "polynomial resources assume completed solver bounds: {forbidden}"
    for required in #[`degree, `overhead, `work, `randomQueries, `hashQueries, `signingQueries,
        `inputWidth, `width, `outputWidth, `routeWidth, `comparisonTime, `scalarTime, `opTime,
        `handlerTickTime, `callerTickTime, `extractionTickTime, `callerCode, `scalarCode, `dynamicCode,
        `structuralCode, `instructionCode, `handlerCode, `solverPortCode] do
      unless fields.contains required do
        throwError "missing polynomial component resource {required}"

run_meta do
  for name in #[``OOPS.GeneralAGM.Family.security_asymptotic,
      ``Proximity.GeneralAGM.Family.security_asymptotic, ``Proximity.GeneralAGM.Family.security_up_to_collision] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      let mut names : Array Name := #[]
      let mut families : Array Name := #[]
      let mut dimensionVaries := false
      for param in params do
        let decl ← getFVarLocalDecl param
        names := names.push decl.userName
        let type ← inferType param
        if #[`degree, `dimension].contains decl.userName then
          unless type.isForall && type.bindingDomain!.isConstOf ``Nat && type.bindingBody!.isConstOf ``Nat do
            throwError "{name}: degree/dimension must vary with the security parameter"
          dimensionVaries := true
        if decl.userName == `hardness then
          unless type.isAppOf ``NativeSolver.Family.dlogNonuniformHardness do
            throwError "{name}: hardness must cover general nonuniform backend solvers"
        if #[`F, `G₁, `G₂, `Gₜ, `K, `M].contains decl.userName then
          unless type.isForall && type.bindingDomain!.isConstOf ``Nat && type.bindingBody!.isSort do
            throwError "{name}: group/label types must vary with the parameter"
          families := families.push decl.userName
        for forbidden in #[``Within, ``NonuniformWithin, `Signatures.Runtime.AGM.SourceCertificate,
            ``NativeSolver.goodProgramTime, ``NativeSolver.badProgramTime] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: completed-solver or arithmetic-source premise {forbidden}"
        if type.isForall then
          let body := type.bindingBody!
          if body.isAppOf ``Finite || body.isAppOf ``Fintype then
            if let .fvar id := body.getAppArgs[0]!.getAppFn then
              if #[`K, `M, `G₂].contains (← id.getUserName) then
                throwError "{name}: finite label/message/public-key domain returned"
      unless families.size == 6 do throwError "{name}: missing varying group/label families"
      unless dimensionVaries do throwError "{name}: missing degree/dimension family"
      for required in #[`parameters, `config, `fixed, `resources, `adversary, `hardness, `fieldGrowth] do
        unless names.contains required do throwError "{name}: missing family hypothesis {required}"
      if name == ``Proximity.GeneralAGM.Family.security_asymptotic then
        unless names.contains `collisionSmall do throwError "Proximity silently discarded collision probability"
      if name == ``Proximity.GeneralAGM.Family.security_up_to_collision then
        if names.contains `collisionSmall then throwError "collision-relative theorem assumes negligible collisions"
        unless (conclusion.find? (fun e => e.isConstOf ``Proximity.LazyAGM.collisionGame)).isSome do
          throwError "collision-relative conclusion lost the original source collision game"
      else
        unless conclusion.isAppOf ``negligible do throwError "{name}: expected negligible forgery success"

end SignaturesTest.WeightedFamilies
