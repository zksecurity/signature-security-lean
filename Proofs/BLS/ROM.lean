import Signatures.BLS.Spec.ROMInternal
import Signatures.BLS.Game
import Signatures.BLS.CoCDH.Spec.LazyGame
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-! The readable BLS handler and the tuple encoding used by the reduction proofs
give exactly the same execution distribution, including the final oracle state. -/

open OracleComp OracleSpec

namespace BLS.ROM

variable {F M G₁ : Type} [SampleableType F] [DecidableEq M] [SMul F G₁]

theorem hashScalar_run_encode (message : M) (state : State F M) :
    Prod.map id Internal.encodeState <$> (hashScalar (F := F) message).run state =
      (Internal.getDlogS (F := F) message).run (Internal.encodeState state) := by
  rcases state with ⟨cache, signed⟩
  cases h : cache message <;>
    simp [hashScalar, Internal.getDlogS, Internal.encodeState, h, StateT.run_bind,
      StateT.run_get, StateT.run_pure, StateT.run_modify, StateT.run_monadLift]

theorem oracle_run_encode (g₁ X₁ : G₁) (request : (advSpec M G₁).Domain)
    (state : State F M) :
    Prod.map id Internal.encodeState <$> (oracle (F := F) g₁ X₁ request).run state =
      (Internal.oracle (F := F) g₁ X₁ request).run (Internal.encodeState state) := by
  rcases request with (n | message) | message
  · simp [oracle, Internal.oracle, StateT.run_monadLift, Internal.encodeState,
      Functor.map_map]
  · simp only [oracle, Internal.oracle, StateT.run_bind, StateT.run_pure, map_bind]
    rw [← hashScalar_run_encode message state]
    simp
  · simp only [oracle, Internal.oracle, StateT.run_bind, StateT.run_modify,
      StateT.run_pure, pure_bind, map_bind]
    have h := hashScalar_run_encode message
      { state with signedMessages := insert message state.signedMessages }
    simp only [Internal.encodeState] at h ⊢
    rw [← h]
    simp

/-- State encoding commutes with every adaptive oracle program. -/
theorem run_encode {α : Type} (g₁ X₁ : G₁) (program : OracleComp (advSpec M G₁) α)
    (state : State F M) :
    Prod.map id Internal.encodeState <$> (simulateQ (oracle (F := F) g₁ X₁) program).run state =
      (simulateQ (Internal.oracle (F := F) g₁ X₁) program).run (Internal.encodeState state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Internal.encodeState (oracle_run_encode g₁ X₁) program state

end BLS.ROM

namespace BLS.ROM

variable (curve : Model.PairingCurve) (securityParameter : Nat) {Message : Type} [DecidableEq Message]

/-- The EUF-CMA experiment with the exponent-keeping oracle: the first simulation
step of the co-CDH reduction, where every hash value `ρ • g₁` is produced from a
remembered exponent `ρ`. `Game.eufCma_eq_rom` shows it has the distribution of the
real game because `g₁` generates. -/
noncomputable def game (adversary : Game.UnrestrictedAdversary curve securityParameter (Message := Message)) : ProbComp Bool := by
  classical
  exact do
    let secret ← ($ᵗ curve.Scalar securityParameter : ProbComp (curve.Scalar securityParameter))
    let ((message, valid), state) ←
      (simulateQ (oracle (F := curve.Scalar securityParameter) (curve.generator securityParameter)
          (secret • curve.generator securityParameter)) (do
        let (message, signature) ← adversary (secret • curve.keyGenerator securityParameter)
        let hash ← ROM.hash message
        return (message, decide (
          BilinearGroup.pairing (F := curve.Scalar securityParameter) (Gₜ := curve.TargetGroup securityParameter)
              signature (curve.keyGenerator securityParameter) =
            BilinearGroup.pairing (F := curve.Scalar securityParameter) (Gₜ := curve.TargetGroup securityParameter)
              hash (secret • curve.keyGenerator securityParameter))))).run State.empty
    return valid && decide (message ∉ state.signedMessages)

/-- The exponent-keeping experiment is exactly the source game of the co-CDH proof. -/
theorem game_eq_source (adversary : Game.UnrestrictedAdversary curve securityParameter (Message := Message)) :
    game curve securityParameter adversary =
      CoCDH.Tight.blsEufLazyPK (F := curve.Scalar securityParameter)
        (Gₜ := curve.TargetGroup securityParameter)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary := by
  classical
  simp only [game, CoCDH.Tight.blsEufLazyPK, CoCDH.Tight.blsEufTightPK,
    ROM.cacheForgeryPK, ROM.cacheForgery, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  apply bind_congr
  intro secret
  have hRun := ROM.run_encode (F := curve.Scalar securityParameter)
    (curve.generator securityParameter) (secret • curve.generator securityParameter)
    (adversary (secret • curve.keyGenerator securityParameter)) ROM.State.empty
  simp only [ROM.Internal.encodeState, ROM.State.empty] at hRun
  rw [← hRun, bind_map_left]

  apply bind_congr
  rintro ⟨⟨message, signature⟩, state⟩
  rcases state with ⟨cache, signed⟩
  cases h : cache message <;>
    simp [ROM.hash, ROM.oracle, ROM.Internal.oracle, ROM.hashScalar, ROM.Internal.getDlogS,
      ROM.Internal.encodeState, h, StateT.run_bind, StateT.run_get, StateT.run_pure,
      StateT.run_modify, StateT.run_monadLift]

end BLS.ROM
