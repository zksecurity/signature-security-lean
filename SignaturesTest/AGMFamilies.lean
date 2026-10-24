import Signatures.BLS.GeneralAGMFamilyStatement
import Lean.Util.CollectAxioms

/-! Check the asymptotic endpoint's actual assumption and axiom scope. The
component-resource record must not smuggle in completed-reduction efficiency,
and arbitrary message/key families must remain supported. -/

open Lean Meta
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.LazyAGM Signatures.Runtime.LazyAGM.NativeSolver
open Signatures.Runtime.LazyAGM.NativeSolver.Family

namespace SignaturesTest.AGMFamilies

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``goodTokenTime_polynomial, ``badTokenTime_polynomial,
      ``goodExtractionTime_polynomial, ``badExtractionTime_polynomial,
      ``goodProgramTime_polynomial, ``badProgramTime_polynomial, ``programDescription_polynomial,
      ``Configuration.nonuniformWithin_of_pointwise,
      ``BLS.GeneralAGM.Family.PolynomialResources.goodTime,
      ``BLS.GeneralAGM.Family.PolynomialResources.badTime,
      ``BLS.GeneralAGM.Family.PolynomialResources.solverCode,
      ``BLS.GeneralAGM.Family.reductions_nonuniform,
      ``BLS.GeneralAGM.Family.Proofs.security, ``BLS.GeneralAGM.Family.security_asymptotic] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

run_meta do
  for name in #[``BLS.GeneralAGM.Family.PolynomialResources.mk,
      ``BLS.GeneralAGM.Family.reductions_nonuniform, ``BLS.GeneralAGM.Family.security_asymptotic] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Within, ``NonuniformWithin, ``Configuration.within,
            ``Configuration.nonuniformWithin, ``dlogWithin, ``dlogNonuniformWithin,
            ``Bounds, ``GeneralCaller.Budget, `Signatures.Runtime.AGM.SourceCertificate,
            ``goodProgramTime, ``badProgramTime, ``programDescription,
            ``BLS.GeneralAGM.Parameters.goodTime, ``BLS.GeneralAGM.Parameters.badTime,
            ``BLS.GeneralAGM.Parameters.solverCode] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: completed-solver budget or arithmetic-source premise {forbidden}"
        forallTelescope type fun _ premise => do
          if premise.isAppOf ``Finite || premise.isAppOf ``Fintype then
            for base in params do
              let declaration ← getFVarLocalDecl base
              if declaration.userName == `M || declaration.userName == `G₂ then
                if (premise.find? (fun e => e == base)).isSome then
                  throwError "{name}: finite message or public-key family required"

run_meta do
  let name := ``BLS.GeneralAGM.Family.security_asymptotic
  forallTelescope (← getConstInfo name).type fun params conclusion => do
    for required in #[`parameters, `config, `fixed, `resources, `adversary, `hardness, `fieldGrowth] do
      unless (← params.anyM fun p => return (← getFVarLocalDecl p).userName == required) do
        throwError "{name}: missing family condition {required}"
    for base in params do
      let declaration ← getFVarLocalDecl base
      if #[`F, `G₁, `G₂, `Gₜ, `M].contains declaration.userName then
        let type ← inferType base
        unless type.isForall && type.bindingDomain!.isConstOf ``Nat && type.bindingBody!.isSort do
          throwError "{name}: {declaration.userName} must vary with the security parameter"
      if declaration.userName == `hardness then
        unless (← inferType base).isAppOf ``dlogNonuniformHardness do
          throwError "{name}: hardness must use the fixed native DLog family class"
      if declaration.userName == `fixed then
        let type ← inferType base
        unless (type.find? (fun e => e.isConstOf ``BLS.GeneralAGM.Parameters.configuration)).isSome do
          throwError "{name}: backend configuration is not fixed across parameters"
    unless conclusion.isAppOf ``negligible &&
        (conclusion.find? (fun e => e.isConstOf ``Model.DirectAGM.game)).isSome &&
        (conclusion.find? (fun e => e.isConstOf ``BLS.LazyAGM.terms)).isSome do
      throwError "{name}: must conclude negligible success in the actual BLS game"
  unless (← findModuleOf? name) == some `Signatures.BLS.GeneralAGMFamilyStatement do
    throwError "family statement moved out of its statement file"
  unless (← findModuleOf? ``BLS.GeneralAGM.Family.Proofs.security) == some `Proofs.BLS.GeneralAGMFamily do
    throwError "family proof must stay in its separate proof file"

-- Zero query allowances still leave initialization/extraction costs. Their
-- polynomiality follows from the same complete formulas; nothing divides by q.
example (overhead : Nat → Nat → Nat) (h : PolynomialOverhead overhead) :
    PolynomiallyBounded (fun n => goodProgramTime (overhead n)
      ⟨n, 0, 0, n, n⟩ n n n n 0 0 n n n n n n n n) := by
  exact goodProgramTime_polynomial overhead (fun n => ⟨n, 0, 0, n, n⟩)
    id id id id (fun _ => 0) (fun _ => 0) id id id id id id id id
    h PolynomiallyBounded.input (PolynomiallyBounded.const 0)
    PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input
    (PolynomiallyBounded.const 0) (PolynomiallyBounded.const 0)
    PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input
    PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input

example (overhead : Nat → Nat → Nat) (h : PolynomialOverhead overhead) :
    PolynomiallyBounded (fun n => badProgramTime (overhead n)
      ⟨n, 0, 0, n, n⟩ n n n n 0 0 n n n n n n n n) := by
  exact badProgramTime_polynomial overhead (fun n => ⟨n, 0, 0, n, n⟩)
    id id id id (fun _ => 0) (fun _ => 0) id id id id id id id id
    h PolynomiallyBounded.input (PolynomiallyBounded.const 0)
    PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input
    (PolynomiallyBounded.const 0) (PolynomiallyBounded.const 0)
    PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input
    PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input PolynomiallyBounded.input

end SignaturesTest.AGMFamilies
