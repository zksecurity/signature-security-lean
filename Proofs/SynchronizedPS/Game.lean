import Proofs.SynchronizedPS.LazyGame

/-! The public algebraic game written out, and its bound by the coefficient game: dropping only
protocol-shape rejection gives the attacker's grouped proof view on the shared lazy base oracle. -/

open OracleComp OracleSpec Model

namespace SynchronizedPS.Game

variable (curve : Model.PairingCurve) (securityParameter : Nat) {Period : Type} [DecidableEq Period]

local notation "𝔽" => curve.Scalar securityParameter
local notation "𝔾₁" => curve.SignatureGroup securityParameter
local notation "𝔾₂" => curve.KeyGroup securityParameter
local notation "𝔾ₜ" => curve.TargetGroup securityParameter
local notation "g₁" => curve.generator securityParameter
local notation "g₂" => curve.keyGenerator securityParameter

/-- The honest signer's reply as the algebraic attacker receives it. -/
noncomputable def sign (x y : 𝔽) (message : Period × 𝔽) : RandomOracle.Computation Period 𝔾₁ 𝔾₁ := do
  let hash ← RandomOracle.hash message.1
  return (x + y * message.2) • hash

/-- The algebraic experiment, written out: generate `(x•g₂, y•g₂)`, run the attacker against the
signer, hash the attacked period, and accept a well-formed interaction whose report passes the
readable game's checks. -/
theorem agm_eq_native (adversary : AlgebraicAdversary curve securityParameter (Period := Period)) :
    agm curve securityParameter adversary = RandomOracle.run do
      let x ← RandomOracle.sample 𝔽
      let y ← RandomOracle.sample 𝔽
      let forgery ← DirectAGM.runWithData (sign curve securityParameter x y) adversary g₁ [x • g₂, y • g₂]
      let hash ← RandomOracle.hash forgery.data.1.1
      return forgery.wellFormed &&
        Proofs.accepts (Gₜ := 𝔾ₜ) g₂ x y forgery.data forgery.signature forgery.signedMessages hash := by
  simp only [agm, EufCma.game, signature, EufCma.Attacker.run, Proofs.accepts,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, Option.map_some, Bool.and_assoc]
  congr!

/-- Dropping only protocol-shape rejection gives exactly the coefficient game. -/
theorem unchecked_eq [Fintype Period] (adversary : AlgebraicAdversary curve securityParameter (Period := Period)) :
    RandomOracle.run (do
      let x ← RandomOracle.sample 𝔽
      let y ← RandomOracle.sample 𝔽
      let forgery ← DirectAGM.runWithData (sign curve securityParameter x y) adversary g₁ [x • g₂, y • g₂]
      let hash ← RandomOracle.hash forgery.data.1.1
      return Proofs.accepts (Gₜ := 𝔾ₜ) g₂ x y forgery.data forgery.signature forgery.signedMessages hash) =
    Proofs.lazyGame (Gₜ := 𝔾ₜ) g₁ g₂ adversary := by
  have key (x y : 𝔽) :
      (DirectAGM.runWithData (sign curve securityParameter x y) adversary g₁ [x • g₂, y • g₂] >>=
        fun forgery => do
          let hash ← RandomOracle.hash forgery.data.1.1
          return Proofs.accepts (Gₜ := 𝔾ₜ) g₂ x y forgery.data forgery.signature forgery.signedMessages hash) =
      ((simulateQ (LazyAGM.handler RandomOracle.random RandomOracle.hash (sign curve securityParameter x y))
          (DirectAGM.ProofView.program (adversary.main ⟨(), LazyAGM.Interactive.groupLists [g₁] [x • g₂, y • g₂]⟩) {})).run ([], []) >>=
        fun value => do
          let hash ← RandomOracle.hash (DirectAGM.ProofView.observeWith g₁ value).1.1.1
          return Proofs.accepts (Gₜ := 𝔾ₜ) g₂ x y (DirectAGM.ProofView.observeWith g₁ value).1
            (DirectAGM.ProofView.observeWith g₁ value).2.1 (DirectAGM.ProofView.observeWith g₁ value).2.2 hash) := by
    have h := congrArg (fun m => m >>= fun p : Forgery 𝔽 Period × 𝔾₁ × List (Period × 𝔽) => do
        let hash ← RandomOracle.hash p.1.1.1
        return Proofs.accepts (Gₜ := 𝔾ₜ) g₂ x y p.1 p.2.1 p.2.2 hash)
      (DirectAGM.runWithData_eq (sign curve securityParameter x y) adversary g₁ [x • g₂, y • g₂])
    simpa only [bind_map_left, DirectAGM.ResultWith.plain] using h
  unfold Proofs.lazyGame RandomOracle.run
  refine congrArg (fun program => (simulateQ (Period →ₒ 𝔾₁).romImpl program).run' ∅) ?_
  refine bind_congr fun x => bind_congr fun y => ?_
  exact key x y

/-- Malformed interactions cannot win, so the native game is bounded by the coefficient game. -/
theorem agm_le [Fintype Period] (adversary : AlgebraicAdversary curve securityParameter (Period := Period)) :
    𝒟[agm curve securityParameter adversary] {true} ≤
      𝒟[Proofs.lazyGame (Gₜ := 𝔾ₜ) g₁ g₂ adversary] {true} := by
  classical
  rw [agm_eq_native, ← unchecked_eq]
  simp only [RandomOracle.run, simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind,
    StateT.run_pure, map_bind, map_pure]
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  rintro ⟨x, cache⟩ _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  rintro ⟨y, cache⟩ _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  rintro ⟨forgery, cache⟩ _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  rintro ⟨hash, cache⟩ _
  by_cases wellFormed : forgery.wellFormed <;> simp [wellFormed]

end SynchronizedPS.Game
