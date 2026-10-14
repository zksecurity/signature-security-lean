import Signatures
import SignaturesTest.FiniteMessages
import Lean.Util.CollectAxioms

open OracleComp OracleSpec BLS.CoCDH.Tight

namespace SignaturesTest.MessageTransport

-- This attacker has an infinite public-key type, as well as infinite messages.
-- Only its finite generated-key family needs a common proof cover.
def key (seed : Bool) : Nat := if seed then 100 else 200

example (adv : TightAdvPK Nat Bool Nat) :
    ∃ cover : Finset Nat, ∃ restricted : TightAdvPK {m // m ∈ cover} Bool Nat,
      ∀ seed, mapMessages Subtype.val (restricted (key seed)) = adv (key seed) :=
  exists_restricted_publicKeys key adv

theorem adaptive_one_sign :
    IsQueryBoundP FiniteMessages.adaptive (fun i => Sum.isRight i = true) 1 := by
  simp [FiniteMessages.adaptive, isQueryBoundP_query_bind_iff]

-- Restriction preserves the actual signing-call bound and the final verification
-- lookup, including the unseen final message from the adaptive regression.
example : IsQueryBoundP
    (restrictMessages _ FiniteMessages.adaptive FiniteMessages.covered)
      (fun i => Sum.isRight i = true) 1 := by
  apply (mapMessages_signing_bound Subtype.val _ 1).mp
  rw [mapMessages_restrictMessages]
  exact adaptive_one_sign

open Lean Meta Elab Command

run_cmd liftTermElabM do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``mapMessages_signing_bound, ``mapMessages_cacheForgery,
      ``run_messageQueries_project, ``projectState_insert, ``projectState_update,
      ``getDlogS_project, ``realOracle_project, ``blsEufTightPK_mapMessages,
      ``blsEufLazyPK_mapMessages, ``map_restrictPublicKeys, ``exists_restricted_publicKeys,
      ``blsEufLazyPK_congr_generated,
      ``BLS.CoCDH.MessageTransport.projectCache_update,
      ``BLS.CoCDH.MessageTransport.randomOracle_project,
      ``BLS.CoCDH.MessageTransport.nativeReply_project,
      ``BLS.CoCDH.MessageTransport.nativeOracle_project,
      ``BLS.CoCDH.MessageTransport.nativeReduction_mapMessages,
      ``BLS.CoCDH.MessageTransport.coronReductionLazyPK_mapMessages,
      ``BLS.CoCDH.MessageTransport.coronReductionLazyPK_congr_at,
      ``BLS.CoCDH.MessageTransport.coCDHExp_coron_congr_generated,
      ``BLS.CoCDH.MessageTransport.coCDHExp_coron_mapMessages,
      ``BLS.CoCDH.Proofs.security_arbitrary_messages] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``exists_restricted_publicKeys, ``BLS.CoCDH.Proofs.security_arbitrary_messages,
      ``Signatures.Runtime.Coron.NativeSolver.security_of_resources,
      ``BLS.Statement.bls_eufcma_of_cocdh_machine_hardness] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          if let .fvar id := type.getAppArgs[0]! then
            if #[`M, `G₂].contains (← id.getUserName) then
              throwError "{name}: added a finite-message/public-key assumption"

end SignaturesTest.MessageTransport
