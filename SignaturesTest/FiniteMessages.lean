import Proofs.BLS.CoCDH.FiniteMessages
import Lean.Util.CollectAxioms

open BLS.ROM

open OracleComp OracleSpec BLS.CoCDH.Tight

namespace SignaturesTest.FiniteMessages

-- Infinite message type, private randomness, an answer-dependent signing
-- message, a repeated hash, and an unseen final-forgery message.
def adaptive : Adversary Nat Bool :=
  (do
    let r : Fin 2 ← query (spec := advSpec Nat Bool) (.inl (.inl 1))
    let b : Bool ← query (spec := advSpec Nat Bool) (.inl (.inr (if r = 0 then 11 else 13)))
    let _ ← query (spec := advSpec Nat Bool) (.inr (if b then 17 else 19))
    let _ ← query (spec := advSpec Nat Bool) (.inl (.inr (if r = 0 then 11 else 13)))
    pure (23, b) : OracleComp (advSpec Nat Bool) (Nat × Bool))

theorem covered : MessageCovered {11, 13, 17, 19, 23} adaptive := by
  simp only [MessageCovered, adaptive, HasQuery.instOfMonadLift_query,
    allPathsSatisfy_query_bind, allPathsSatisfy_pure]
  simp
  intro r
  split_ifs <;> simp <;> exact em _

example : MessageCovered {11, 13, 17, 19, 23} (cacheForgery adaptive) :=
  covered.cacheForgery

example : mapMessages Subtype.val (restrictMessages _ adaptive covered) = adaptive :=
  mapMessages_restrictMessages _ adaptive covered

open Lean Meta Elab Command

run_cmd liftTermElabM do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Signatures.FiniteDomain.allPaths_mono,
      ``Signatures.FiniteDomain.exists_cover, ``Signatures.FiniteDomain.exists_family_cover,
      ``exists_message_cover, ``mapMessages_query_bind, ``restrictMessages_random,
      ``restrictMessages_hash, ``restrictMessages_sign, ``mapMessages_restrictMessages,
      ``MessageCovered.cacheForgery, ``exists_restricted_family] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``exists_message_cover, ``exists_restricted_family] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          if let .fvar id := type.getAppArgs[0]! then
            if (← id.getUserName) == `M then
              throwError "{name}: finite-message assumption returned"

end SignaturesTest.FiniteMessages
