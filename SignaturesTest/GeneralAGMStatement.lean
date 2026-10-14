import Signatures.BLS.GeneralAGMStatement
import Lean.Util.CollectAxioms

/-! Guard the public statement and its underlying resource theorem. In
particular, bundling must not hide a finished-solver budget or an arithmetic
attacker requirement, and the message/public-key types stay unrestricted. -/

open Lean Meta
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.LazyAGM.NativeSolver

namespace SignaturesTest.GeneralAGMStatement

-- Keep the public signatures small: parameters/adversary, or a parameter
-- family/security parameter/adversary. Resource proofs belong in the records.
run_meta do
  for (name, expected) in #[( ``BLS.GeneralAGM.security, 2), (``BLS.GeneralAGM.Family.security, 3)] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      let mut explicitCount := 0
      for param in params do
        if (← getFVarLocalDecl param).binderInfo == .default then
          explicitCount := explicitCount + 1
      unless explicitCount == expected do
        throwError "{name}: expected {expected} explicit public arguments, found {explicitCount}"

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Model.le_advantageBound, ``Model.hardWithin_advantageBound, ``Model.advantageBound_le,
      ``challenge_size, ``security_of_resources, ``BLS.GeneralAGM.security, ``BLS.GeneralAGM.Family.security] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

run_meta do
  for name in #[``security_of_resources, ``BLS.GeneralAGM.security,
      ``BLS.GeneralAGM.Family.security, ``BLS.GeneralAGM.Parameters.mk, ``BLS.GeneralAGM.AlgebraicAdversary.mk] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Bounds, ``GeneralCaller.Budget,
            `Signatures.Runtime.AGM.SourceCertificate,
            `Signatures.Runtime.Coron.SourceCertificate,
            `Signatures.Runtime.Schnorr.SourceCertificate] do
          if type.find? (fun e => e.isConstOf forbidden) |>.isSome then
            throwError "{name}: hidden completed-code budget or arithmetic attacker: {forbidden}"
        forallTelescope type fun _ premise => do
          if premise.isAppOf ``Finite || premise.isAppOf ``Fintype then
            for base in params do
              let declaration ← getFVarLocalDecl base
              if declaration.userName == `M || declaration.userName == `G₂ then
                if premise.find? (fun e => e == base) |>.isSome then
                  throwError "{name}: finite message or public-key domain required"

-- The public bound and its implementation/resource class stay inspectable.
run_meta do
  let info ← getConstInfo ``BLS.GeneralAGM.Parameters.securityBound
  unless info.value?.isSome do
    throwError "securityBound must be a transparent definition"
  let info ← getConstInfo ``BLS.GeneralAGM.Parameters.dlogBound
  unless info.value?.isSome do
    throwError "dlogBound must expose its implementation/resource class"

end SignaturesTest.GeneralAGMStatement
