import Signatures.Proximity.GeneralAGMParameters
import Signatures.Runtime.GeneralWeightedCertificates
import Signatures.Proximity.Proofs.LazyAGMArbitrarySlots

/-! Concrete Proximity security for general realized algebraic attackers.
Both complete native reduction certificates are derived before applying hardness.
The original source game and its probability loss are preserved. -/

open BilinearGroup

open OracleComp OracleSpec PFunctor AlgebraicGroupModel
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM

open Signatures.Runtime.WeightedAGM.NativeSolver

namespace Proximity.GeneralAGM

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]


variable {dimension : Nat}
  (P : Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (K := K) (M := M) dimension)
  (A : AlgebraicAdversary P)

theorem reductions_within :
    dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
      P.generator P.keyGenerator P.inputWidth P.solverCode P.goodTime
      (Model.LazyAGM.WeightedReduction.goodReductionList (Proximity.LazyAGM.terms) A.source) ∧
    dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
      P.generator P.keyGenerator P.inputWidth P.solverCode P.badTime
      (Model.LazyAGM.WeightedReduction.badReductionList (Proximity.LazyAGM.terms) A.source) := by
  have h := General.reductions_within P (A.native P)
  constructor
  · rw [← goodReduction_encoded (M := M) P.cost A.source]
    exact h.1
  · rw [← badReduction_encoded (M := M) P.cost A.source]
    exact h.2

variable [Fintype F] [SampleableType G₁] [Fintype G₁] [DecidableEq Gₜ]

theorem security :
    𝒟[Proximity.LazyAGM.game (Gₜ := Gₜ) P.generator P.keyGenerator A.source] {true} ≤ P.securityBound +
      𝒟[Proximity.LazyAGM.collisionGame P.keyGenerator A.source] {true} := by
  obtain ⟨goodFits, badFits⟩ := reductions_within P A
  have goodBound := Model.le_advantageBound (Model.dlog11Advantage P.generator P.keyGenerator) _ _ goodFits
  have badBound := Model.le_advantageBound (Model.dlog11Advantage P.generator P.keyGenerator) _ _ badFits
  exact (Proximity.LazyAGM.Proofs.security_arbitrary_slots P.generator P.keyGenerator A.source P.generates P.pairingInjective).trans
    (add_le_add (add_le_add (add_le_add goodBound badBound) le_rfl) le_rfl)

theorem security_of_hardness (goodEpsilon badEpsilon : ENNReal)
    (goodHardness : Model.HardWithin (Model.dlog11Advantage (F := F) P.generator P.keyGenerator)
      (dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
        P.generator P.keyGenerator P.inputWidth P.solverCode) P.goodTime goodEpsilon)
    (badHardness : Model.HardWithin (Model.dlog11Advantage (F := F) P.generator P.keyGenerator)
      (dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
        P.generator P.keyGenerator P.inputWidth P.solverCode) P.badTime badEpsilon) :
    𝒟[Proximity.LazyAGM.game (Gₜ := Gₜ) P.generator P.keyGenerator A.source] {true} ≤
      goodEpsilon + badEpsilon + 1 / (Fintype.card F : ENNReal) +
      𝒟[Proximity.LazyAGM.collisionGame P.keyGenerator A.source] {true} := by
  obtain ⟨goodFits, badFits⟩ := reductions_within P A
  exact (Proximity.LazyAGM.Proofs.security_arbitrary_slots P.generator P.keyGenerator A.source P.generates P.pairingInjective).trans
    (add_le_add (add_le_add (add_le_add (goodHardness _ goodFits) (badHardness _ badFits)) le_rfl) le_rfl)

end Proximity.GeneralAGM
