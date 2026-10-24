import Signatures.OOPS.GeneralAGMParameters
import Proofs.Runtime.GeneralWeightedCertificates
import Proofs.OOPS.LazyAGMArbitraryTopics

/-! Concrete OOPS security for general realized algebraic attackers.
Both complete native reduction certificates are derived before applying hardness.
The original source game and its probability loss are preserved. -/

open BilinearGroup

open OracleComp OracleSpec PFunctor AlgebraicGroupModel
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM

open Signatures.Runtime.WeightedAGM.NativeSolver

namespace OOPS.GeneralAGM

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]


variable {degree : Nat}
  (P : Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (K := K) (M := M) degree)
  (A : AlgebraicAdversary P)

theorem reductions_within :
    dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
      P.generator P.keyGenerator P.inputWidth P.solverCode P.goodTime
      (Model.LazyAGM.WeightedReduction.goodReductionList (OOPS.LazyAGM.terms degree) A.proofView) ∧
    dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
      P.generator P.keyGenerator P.inputWidth P.solverCode P.badTime
      (Model.LazyAGM.WeightedReduction.badReductionList (OOPS.LazyAGM.terms degree) A.proofView) := by
  have h := General.reductions_within P A.native
  have ht : Index.sourceTerms (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) P.cost (.oops degree) = OOPS.LazyAGM.terms degree :=
    funext (Index.oops_sourceTerms P.cost degree)
  simpa only [ht, AlgebraicAdversary.native] using h

variable [Fintype F] [SampleableType G₁] [Fintype G₁] [DecidableEq Gₜ]

theorem security :
    𝒟[Model.DirectAGM.game (Gₜ := Gₜ) (OOPS.LazyAGM.terms degree) (OOPS.LazyAGM.admissible degree)
      P.generator P.keyGenerator A.source] {true} ≤ P.securityBound := by
  obtain ⟨goodFits, badFits⟩ := reductions_within P A
  have goodBound := Model.le_advantageBound (Model.dlog11Advantage P.generator P.keyGenerator) _ _ goodFits
  have badBound := Model.le_advantageBound (Model.dlog11Advantage P.generator P.keyGenerator) _ _ badFits
  apply (Model.DirectAGM.game_le (OOPS.LazyAGM.terms degree) (OOPS.LazyAGM.admissible degree)
    P.generator P.keyGenerator A.source).trans
  simpa only [OOPS.LazyAGM.game_eq_of_decidableEq, AlgebraicAdversary.proofView,
    General.Parameters.securityBound, General.Parameters.dlogBound] using
    (OOPS.LazyAGM.Proofs.security_arbitrary_topics P.generator P.keyGenerator degree A.proofView P.generates P.pairingInjective).trans
    (add_le_add (add_le_add goodBound badBound) le_rfl)

theorem security_of_hardness (goodEpsilon badEpsilon : ENNReal)
    (goodHardness : Model.HardWithin (Model.dlog11Advantage (F := F) P.generator P.keyGenerator)
      (dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
        P.generator P.keyGenerator P.inputWidth P.solverCode) P.goodTime goodEpsilon)
    (badHardness : Model.HardWithin (Model.dlog11Advantage (F := F) P.generator P.keyGenerator)
      (dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
        P.generator P.keyGenerator P.inputWidth P.solverCode) P.badTime badEpsilon) :
    𝒟[Model.DirectAGM.game (Gₜ := Gₜ) (OOPS.LazyAGM.terms degree) (OOPS.LazyAGM.admissible degree)
      P.generator P.keyGenerator A.source] {true} ≤
      goodEpsilon + badEpsilon + 1 / (Fintype.card F : ENNReal) := by
  obtain ⟨goodFits, badFits⟩ := reductions_within P A
  apply (Model.DirectAGM.game_le (OOPS.LazyAGM.terms degree) (OOPS.LazyAGM.admissible degree)
    P.generator P.keyGenerator A.source).trans
  simpa only [OOPS.LazyAGM.game_eq_of_decidableEq, AlgebraicAdversary.proofView,
    General.Parameters.securityBound, General.Parameters.dlogBound] using
    (OOPS.LazyAGM.Proofs.security_arbitrary_topics P.generator P.keyGenerator degree A.proofView P.generates P.pairingInjective).trans
    (add_le_add (add_le_add (goodHardness _ goodFits) (badHardness _ badFits)) le_rfl)

end OOPS.GeneralAGM
