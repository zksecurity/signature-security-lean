import Signatures.BLS.Proofs.LazyAGMArbitraryMessages
import Signatures.BLS.Proofs.LazyAGMList
import Lean.Util.CollectAxioms

open OracleComp OracleSpec Model.LazyAGM BLS.LazyAGM.MessageTransport

namespace SignaturesTest.LazyAGMTransport

-- Infinite messages and public keys; finite replies still give a finite proof
-- cover at every generated key, including every private-coin/adaptive branch.
def adaptive : Adversary Nat Nat Nat Bool Nat where
  main pk := do
    let bit : Fin 2 ← liftM ((advSpec Nat Nat Bool).query (.inl (.inl 1)))
    let hashed : Bool ← liftM ((advSpec Nat Nat Bool).query (.inl (.inr (pk + bit.val))))
    let _ : Bool ← liftM ((advSpec Nat Nat Bool).query (.inr (if hashed then pk + 2 else pk + 3)))
    let _ : Bool ← liftM ((advSpec Nat Nat Bool).query (.inl (.inr pk)))
    pure ⟨pk + 10, 7, [11, 12, 13], [14, 15]⟩

def cover : Finset Nat := {0, 1, 2, 3, 10}

theorem covered : MessageCovered cover (adaptive.main 0) := by
  simp only [MessageCovered, adaptive, allPathsSatisfy_query_bind, allPathsSatisfy_pure]
  simp [cover]
  intro bit
  change Fin 2 at bit
  fin_cases bit <;> simp

-- The original complete program is recovered, including coefficients whose
-- list lengths differ from the actual transcript lengths.
example : mapMain Subtype.val (restrictMain cover (adaptive.main 0) covered) = adaptive.main 0 :=
  mapMain_restrictMain cover (adaptive.main 0) covered

-- A cover containing only queried messages is insufficient: final verification
-- must still hash the previously unseen final forgery message.
example : ¬ MessageCovered ({0, 1, 2, 3} : Finset Nat) (adaptive.main 0) := by
  simp only [MessageCovered, adaptive, allPathsSatisfy_query_bind, allPathsSatisfy_pure]
  simp

def key (seed : Bool) : Nat := if seed then 100 else 0

example : ∃ cover : Finset Nat,
    ∃ restricted : Adversary Nat {m // m ∈ cover} {m // m ∈ cover} Bool Nat,
      ∀ seed, (mapAdversary Subtype.val restricted).main (key seed) = adaptive.main (key seed) :=
  exists_restricted_publicKeys key adaptive

-- Renaming preserves the repeated occurrences in both transcripts, not just
-- the set of queried messages.
example : mapTranscript Nat.succ ([(0, true), (0, true)], [(2, false)]) =
    ([(1, true), (1, true)], [(3, false)]) := rfl

open Lean Meta Elab Command

run_cmd liftTermElabM do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``exists_message_cover, ``mapMain_restrictMain, ``exists_restricted_publicKeys,
      ``BLS.CoCDH.MessageTransport.projectCache_update,
      ``BLS.CoCDH.MessageTransport.randomOracle_project,
      ``BLS.CoCDH.MessageTransport.baseQueries_lift,
      ``BLS.CoCDH.MessageTransport.lazyQuery_project,
      ``BLS.CoCDH.MessageTransport.lazyRun_project,
      ``BLS.CoCDH.MessageTransport.lazyRun_rename,
      ``privateSim_map, ``privateRun_map, ``traceTerms_map, ``evalTerms_map,
      ``goodProgram_map, ``badProgram_map, ``goodReduction_map, ``badReduction_map,
      ``materialize_map, ``fresh_map, ``run_eq_private, ``experiment_map, ``game_map,
      ``goodReduction_congr_at, ``badReduction_congr_generated,
      ``goodExp_congr_generated, ``badExp_congr_generated, ``game_congr_generated,
      ``BLS.LazyAGM.Reduction.security_arbitrary_messages,
      ``BLS.LazyAGM.Reduction.security_arbitrary_messages_list] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``exists_restricted_publicKeys, ``goodReduction_map, ``badReduction_map,
      ``experiment_map, ``game_map, ``BLS.CoCDH.MessageTransport.lazyRun_rename,
      ``BLS.LazyAGM.Reduction.security_arbitrary_messages,
      ``BLS.LazyAGM.Reduction.security_arbitrary_messages_list] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          if let .fvar id := type.getAppArgs[0]! then
            if #[`N, `M, `G₂].contains (← id.getUserName) then
              throwError "{name}: added a finite-message/public-key premise"

end SignaturesTest.LazyAGMTransport
