import Proofs.Runtime.BackendSchnorrAGMCallerBudget
import Lean.Util.CollectAxioms

open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.SchnorrAGM.Native

namespace SignaturesTest.BackendSchnorrAGMBudget

-- Check both the public theorem types and the records supplying primitive/port
-- contracts. A new wrapper cannot hide a completed handler budget in a record.
open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``retainedTag_bound_of_width, ``Handler.frame_widths, ``Handler.args_size,
      ``Handler.reply_size, ``Handler.store_size, ``Handler.nativeRequest_size,
      ``Handler.code_bound_of_components, ``Handler.code_bound, ``Handler.reserved_weaken,
      ``Handler.reserved_lower, ``Handler.primitiveCaps_restrict, ``Handler.code_bound_reserved,
      ``Handler.executed_mem_code, ``Handler.caller_bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``Handler.PortCaps.mk, ``Handler.PrimitiveCaps.mk, ``Handler.code_bound,
      ``Handler.code_bound_reserved, ``Handler.caller_bound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: unexpected finite-domain premise"
        for forbidden in #[``Handler.code, ``Handler.caller, ``Handler.random, ``Handler.group,
            ``Handler.inner, ``Handler.dispatch, ``Handler.groupCode, ``Handler.timeBudget,
            ``HandlerComponents.random, ``HandlerComponents.hash, ``HandlerComponents.signing,
            ``HandlerComponents.localCode, ``Random.code, ``HashDispatch.code, ``SigningDispatch.code,
            ``Signing.code, ``Hash.code, ``Read.code, `Signatures.Runtime.AGM.SourceCertificate,
            `Signatures.Runtime.Schnorr.SourceCertificate] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            -- A caller bound is applied to an observed supported execution;
            -- membership is not an assumed runtime certificate.
            unless name == ``Handler.caller_bound && forbidden == ``Handler.caller && type.isAppOf ``Membership.mem do
              throwError "{name}: assumes finished reduction work or restricts attacker implementation ({forbidden})"
        if name != ``Handler.caller_bound &&
            (type.find? (fun e => e.isConstOf ``GeneralCaller.Budget)).isSome then
          throwError "{name}: unexpected caller budget in a local contract"

end SignaturesTest.BackendSchnorrAGMBudget
