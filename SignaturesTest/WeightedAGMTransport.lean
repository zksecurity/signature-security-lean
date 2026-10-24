import Proofs.OOPS.LazyAGMArbitraryTopics
import Proofs.Proximity.LazyAGMArbitrarySlots
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec Model.LazyAGM Model.LazyAGM.WeightedTransport
open BLS.LazyAGM.MessageTransport (mapOutput)

namespace SignaturesTest.WeightedAGMTransport

-- Infinite topics and public keys, with distinct index/message types. Later
-- labels depend on private coins and a returned point; output coefficients
-- deliberately have lengths different from the received transcripts.
def adaptive : Adversary Nat (Nat × Fin 2) (Nat × Nat) Bool Nat where
  main pk := do
    let bit : Fin 2 ← liftM ((advSpec (Nat × Fin 2) (Nat × Nat) Bool).query (.inl (.inl 1)))
    let hashed : Bool ← liftM ((advSpec (Nat × Fin 2) (Nat × Nat) Bool).query
      (.inl (.inr (pk + bit.val, 0))))
    let _ : Bool ← liftM ((advSpec (Nat × Fin 2) (Nat × Nat) Bool).query
      (.inr (42, if hashed then pk + 2 else pk + 3)))
    let _ : Bool ← liftM ((advSpec (Nat × Fin 2) (Nat × Nat) Bool).query (.inl (.inr (pk, 1))))
    pure ⟨(99, pk + 10), 7, [11, 12, 13], [14, 15]⟩

def cover : Finset Nat := {0, 1, 2, 3, 10}

theorem covered : LabelCovered Prod.fst Prod.snd cover (adaptive.main 0) := by
  simp only [LabelCovered, adaptive, allPathsSatisfy_query_bind, allPathsSatisfy_pure]
  simp [cover]
  intro bit
  change Fin 2 at bit
  fin_cases bit <;> simp

-- Covering only requests is insufficient; final-target evaluation is included.
example : ¬ LabelCovered Prod.fst Prod.snd ({0, 1, 2, 3} : Finset Nat) (adaptive.main 0) := by
  simp only [LabelCovered, adaptive, allPathsSatisfy_query_bind, allPathsSatisfy_pure]
  simp

-- Every reply branch matters, not just the successful/first Boolean reply.
example : ¬ LabelCovered Prod.fst Prod.snd ({0, 1, 2, 10} : Finset Nat) (adaptive.main 0) := by
  simp only [LabelCovered, adaptive, allPathsSatisfy_query_bind, allPathsSatisfy_pure]
  simp

private def topicIndex : {t // t ∈ cover} × Fin 2 → Nat × Fin 2 :=
  OOPS.LazyAGM.TopicTransport.index Subtype.val

private def topicMessage : Nat × {t // t ∈ cover} → Nat × Nat :=
  OOPS.LazyAGM.TopicTransport.message Subtype.val

theorem liftable : Liftable topicIndex topicMessage (adaptive.main 0) := by
  apply LabelCovered.liftable Prod.fst Prod.snd cover topicIndex topicMessage ?_ ?_ _ covered
  · intro i hi
    exact ⟨(⟨i.1, hi⟩, i.2), rfl⟩
  · intro m hm
    exact ⟨(m.1, ⟨m.2, hm⟩), rfl⟩

example : mapMain topicIndex topicMessage
    (restrictMain topicIndex topicMessage (adaptive.main 0) liftable) = adaptive.main 0 :=
  mapMain_restrictMain topicIndex topicMessage (adaptive.main 0) liftable

def key (seed : Bool) : Nat := if seed then 100 else 0

example : ∃ cover : Finset Nat, ∀ seed,
    LabelCovered Prod.fst Prod.snd cover (adaptive.main (key seed)) :=
  exists_label_cover Prod.fst Prod.snd (fun seed => adaptive.main (key seed))

-- Both occurrence lists retain their order and multiplicity under distinct maps.
example : mapTranscript Nat.succ (fun p : Nat × Bool => (p.1 + 10, p.2))
    ([(0, true), (0, false)], [((2, true), false), ((2, true), true)]) =
    ([(1, true), (1, false)], [((12, true), false), ((12, true), true)]) := rfl

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def collisionOutput : Output (ZMod 5) ((Fin 1 → ZMod 5) × Nat) :=
  ⟨(fun _ => 2, 10), 0, [], [2, 4]⟩

private def signed : List ((Fin 1 → ZMod 5) × Nat) := [(fun _ => 1, 7)]

-- Other slots still contribute to the collision term, and an extra coefficient
-- has no matching signed message. Injective slot transport preserves the event.
example : Proximity.LazyAGM.Collision collisionOutput signed := by
  unfold Proximity.LazyAGM.Collision
  decide

example : Proximity.LazyAGM.Collision
    (mapOutput (Proximity.LazyAGM.SlotTransport.message Nat.succ) collisionOutput)
    (signed.map (Proximity.LazyAGM.SlotTransport.message Nat.succ)) := by
  rw [Proximity.LazyAGM.SlotTransport.collision_map Nat.succ Nat.succ_injective]
  unfold Proximity.LazyAGM.Collision
  decide

-- Injectivity matters: merging slots can destroy exact-pair freshness.
private def sameVector : Output (ZMod 5) ((Fin 1 → ZMod 5) × Nat) :=
  ⟨(fun _ => 1, 10), 0, [], [1]⟩

example : Proximity.LazyAGM.Collision sameVector signed := by
  unfold Proximity.LazyAGM.Collision
  decide

example : ¬ Proximity.LazyAGM.Collision
    (mapOutput (Proximity.LazyAGM.SlotTransport.message (fun _ : Nat => 0)) sameVector)
    (signed.map (Proximity.LazyAGM.SlotTransport.message (fun _ : Nat => 0))) := by
  unfold Proximity.LazyAGM.Collision
  decide

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``exists_label_cover, ``LabelCovered.liftable, ``mapMain_restrictMain,
      ``restrictPublicKeys_map_at, ``privateSim_map, ``privateRun_map, ``signedTerms_map,
      ``goodProgram_map, ``badProgram_map, ``goodReduction_map, ``badReduction_map,
      ``materialize_map, ``fresh_map, ``experiment_map, ``game_map,
      ``goodExp_congr_generated, ``badExp_congr_generated, ``game_congr_generated,
      ``OOPS.LazyAGM.TopicTransport.admissible_map,
      ``OOPS.LazyAGM.TopicTransport.exists_restricted_publicKeys,
      ``OOPS.LazyAGM.Proofs.security_arbitrary_topics,
      ``Proximity.LazyAGM.SlotTransport.collision_map,
      ``Proximity.LazyAGM.SlotTransport.collisionGame_map,
      ``Proximity.LazyAGM.SlotTransport.collisionGame_congr_generated,
      ``Proximity.LazyAGM.SlotTransport.exists_restricted_publicKeys,
      ``Proximity.LazyAGM.Proofs.security_arbitrary_slots] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``exists_label_cover, ``goodReduction_map, ``badReduction_map, ``game_map,
      ``OOPS.LazyAGM.TopicTransport.exists_restricted_publicKeys,
      ``OOPS.LazyAGM.Proofs.security_arbitrary_topics,
      ``Proximity.LazyAGM.SlotTransport.collisionGame_map,
      ``Proximity.LazyAGM.SlotTransport.exists_restricted_publicKeys,
      ``Proximity.LazyAGM.Proofs.security_arbitrary_slots] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          if let .fvar id := type.getAppArgs[0]! then
            if #[`ι, `κ, `M, `N, `T, `S, `U, `G₂].contains (← id.getUserName) then
              throwError "{name}: finite index/message/topic/slot/public-key premise"

end SignaturesTest.WeightedAGMTransport
