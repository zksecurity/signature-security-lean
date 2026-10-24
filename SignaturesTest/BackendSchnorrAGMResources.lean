import Proofs.Runtime.BackendSchnorrAGMOutputSize
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.SchnorrAGM.Native
open Signatures.Runtime.SchnorrAGM.Native.Interface

namespace SignaturesTest.BackendSchnorrAGMResources

section Recovery

variable {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass C}
  (rep : LanguageRepresentation C (cryptoBase Nat Nat Nat Nat Nat))
  {header : Nat} (sizes : SizeLaws Q header)
  (lengths : ListLengthLaws Q rep.data) (payloads : ListPayloadLaws Q rep.data)

-- Signing ignores coefficient rows semantically, but even an unused second
-- row must fit in the actual encoded request. Messages have an infinite type.
example (m : Nat) (row : List Nat) (width : Nat)
    (natural : NatValueLaws Q rep.data)
    (encoded : Q.size (positions rep) (encodeRequest (request (.sign m) [] [[], row])) ≤ width) :
    row.length ≤ width := by
  have h := Handler.nativeRequestBound_of_size rep sizes lengths payloads natural
    (encodeRequest (request (.sign m) [] [[], row])) width encoded
  exact h.coefficients row (by simp [request])

-- A malformed final forgery with two rows still pays for the full output.
-- No accepted-shape or representation-length premise is supplied separately.
example (m z : Nat) (row : List Nat) (width : Nat)
    (encoded : Q.size (rep.ty forgeryTy) ((m, z), [], [[], row]) ≤ width) :
    row.length ≤ width ∧ 2 ≤ width := by
  have h := Handler.forgeryBound_of_size rep sizes lengths payloads
    (decodeForgery ((m, z), [], [[], row])) width encoded
  exact ⟨h.coefficients row (by simp [decodeForgery]), h.rows⟩

-- Binary arities are allowed to reach the entire exponential numeric range.
-- Their encoding width, not that range's cardinality, supplies the width cap.
example (bits header : Nat)
    (lower : ∀ n, Nat.size n ≤ Q.size rep.data.nat n)
    (upper : ∀ n, Q.size rep.data.nat n ≤ Nat.size n + header) :
    (NatValueLaws.binary lower).capacity bits = 2 ^ bits - 1 ∧
      Q.size rep.data.nat ((NatValueLaws.binary lower).capacity bits) ≤ bits + header :=
  ⟨rfl, NatValueLaws.binary_width header bits _ upper le_rfl⟩

end Recovery

-- Resource substitution must not smuggle a caller invariant, a complete
-- reduction budget, finite message/group universes or an arithmetic attacker
-- restriction into a theorem or one of its contract records.
open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``ListPayloadLaws.member_size_le, ``ListPayloadLaws.of_additive,
      ``NatValueLaws.binary, ``NatValueLaws.binary_width,
      ``decode_encodeForgery, ``encode_decodeForgery,
      ``Handler.argsBound_mono, ``Handler.nativeRequestBound_mono, ``Handler.requestBound_mono,
      ``Handler.argsBound_of_size, ``Handler.nativeRequestBound_of_size,
      ``Handler.recovery_of_encoding, ``Handler.canonicalRecovery,
      ``Handler.reachable_request, ``Handler.reachable_output, ``Handler.resource_step,
      ``Handler.caller_bound_of_resources, ``Handler.caller_reference_denote,
      ``Handler.caller_output_invariant, ``Handler.caller_output_size_of_resources,
      ``Handler.caller_no_cutoff_of_resources, ``Handler.caller_source_of_resources,
      ``Handler.canonicalOutputRecovery, ``Handler.forgeryBound_of_size,
      ``Handler.forgeryBound_of_output_size, ``Handler.caller_forgery_of_resources] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``Handler.RequestRecovery.mk, ``Handler.OutputRecovery.mk,
      ``Handler.PortCaps.mk, ``Handler.PrimitiveCaps.mk,
      ``Handler.recovery_of_encoding, ``Handler.canonicalRecovery, ``Handler.canonicalOutputRecovery,
      ``Handler.caller_bound_of_resources, ``Handler.caller_output_size_of_resources,
      ``Handler.caller_no_cutoff_of_resources, ``Handler.caller_source_of_resources,
      ``Handler.caller_forgery_of_resources] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: unexpected finite-domain premise"
        for forbidden in #[``GeneralCaller.Budget, ``GeneralCaller.Reachable,
            ``Handler.code, ``Handler.caller, ``Handler.timeBudget,
            ``HandlerComponents.random, ``HandlerComponents.hash, ``HandlerComponents.signing,
            ``Random.code, ``HashDispatch.code, ``SigningDispatch.code, ``Read.code,
            `Signatures.Runtime.AGM.SourceCertificate, `Signatures.Runtime.Schnorr.SourceCertificate] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            unless forbidden == ``Handler.caller && type.isAppOf ``Membership.mem do
              throwError "{name}: unexpected whole-program budget or attacker restriction ({forbidden})"

end SignaturesTest.BackendSchnorrAGMResources
