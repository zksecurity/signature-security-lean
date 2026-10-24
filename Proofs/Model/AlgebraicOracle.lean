import Signatures.Model.AlgebraicOracle
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-! Exact correspondence between the record-state oracle and the grouped
transcript used by the existing certified AGM interaction and reduction proofs. -/

open OracleComp OracleSpec

namespace Model.AlgebraicOracle

def encodeState {Index Message Group : Type} (state : State Index Message Group) :
    LazyAGM.Transcript Index Message Group := (state.hashReplies, state.signingReplies)

theorem oracle_run_encode {Index Message Group : Type} {N : Type → Type}
    [Monad N] [LawfulMonad N] (random : QueryImpl unifSpec N)
    (hash : Index → N Group) (sign : Message → N Group)
    (request : (LazyAGM.advSpec Index Message Group).Domain) (state : State Index Message Group) :
    Prod.map id encodeState <$> (oracle random hash sign request).run state =
      (LazyAGM.handler random hash sign request).run (encodeState state) := by
  rcases request with (n | index) | message <;>
    simp [oracle, LazyAGM.handler, encodeState, StateT.run_bind, StateT.run_monadLift,
      StateT.run_modify, Functor.map_map]

theorem run_encode {Index Message Group α : Type} {N : Type → Type}
    [Monad N] [LawfulMonad N] (random : QueryImpl unifSpec N)
    (hash : Index → N Group) (sign : Message → N Group)
    (program : OracleComp (LazyAGM.advSpec Index Message Group) α) (state : State Index Message Group) :
    Prod.map id encodeState <$> (simulateQ (oracle random hash sign) program).run state =
      (simulateQ (LazyAGM.handler random hash sign) program).run (encodeState state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ encodeState
    (oracle_run_encode random hash sign) program state

variable {F Index Message G₁ G₂ : Type} [Field F] [AddCommGroup G₁] [Module F G₁]

/-- Preserve the candidate, every visible reply, and every signing coefficient. -/
theorem run_eq (terms : Message → List (Index × F)) (secret : F)
    (adversary : LazyAGM.Adversary F Index Message G₁ G₂) (generator : G₁) (publicKey : G₂) :
    run terms secret adversary generator publicKey =
      (fun (output, transcript) => ({
        message := output.mstar
        signature := LazyAGM.materialize generator output transcript
        signedMessages := transcript.2.map Prod.fst
        signingCoefficients := output.ξ } : Result F Message G₁)) <$>
      LazyAGM.run terms secret adversary publicKey := by
  have hRun := run_encode Model.RandomOracle.random Model.RandomOracle.hash (sign terms secret)
    (adversary.main publicKey) (State.empty (Index := Index))
  change _ = LazyAGM.run terms secret adversary publicKey at hRun
  rw [← hRun]
  simp [run, Functor.map_map, encodeState, State.signedMessages,
    LazyAGM.materialize_eq_weightedReplies]

variable [SampleableType F] [SampleableType G₁] [DecidableEq Index]
  [AddCommGroup G₂] [Module F G₂]

/-- The readable experiment is exactly the certified AGM source game. -/
theorem game_eq {Gₜ : Type} [AddCommGroup Gₜ] [Module F Gₜ]
    [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]
    (terms : Message → List (Index × F)) (admissible : Message → List Message → Prop)
    (generator : G₁) (keyGenerator : G₂) (adversary : LazyAGM.Adversary F Index Message G₁ G₂) :
    (by
      classical
      exact RandomOracle.run do
        let secret ← RandomOracle.sample F
        let forgery ← run terms secret adversary generator (secret • keyGenerator)
        let hash ← hashMessage terms forgery.message
        return decide (admissible forgery.message forgery.signedMessages ∧
          BilinearGroup.pairing (F := F) (Gₜ := Gₜ) forgery.signature keyGenerator =
            BilinearGroup.pairing (F := F) (Gₜ := Gₜ) hash (secret • keyGenerator) ∧
          forgery.message ∉ forgery.signedMessages)) =
      LazyAGM.game (Gₜ := Gₜ) terms admissible generator keyGenerator adversary := by
  classical
  simp only [RandomOracle.run, LazyAGM.game, LazyAGM.experiment_eq, run_eq,
    bind_map_left, hashMessage]
  rfl

end Model.AlgebraicOracle
