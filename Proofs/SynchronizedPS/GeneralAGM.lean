import Signatures.SynchronizedPS.GeneralAGMParameters
import Proofs.Runtime.GeneralSyncWrapAdversary
import Proofs.SynchronizedPS.PeriodTransport
import Proofs.SynchronizedPS.Game

/-! Concrete synchronized PS security for general realized algebraic attackers. The coefficient
game and the public game are bounded by the average over the known key `k` of the four named
per-key solvers' DLog successes, and each per-key solver is in its derived budget at every `k`. -/

open BilinearGroup
open OracleComp OracleSpec PFunctor AlgebraicGroupModel
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.WeightedAGM
open Signatures.Runtime.WeightedAGM.NativeSolver

namespace SynchronizedPS.GeneralAGM

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasComposition] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]
  {generator : G₁} {keyGenerator : G₂}
  (P : Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (K := K) (M := M) generator keyGenerator)
  (A : AlgebraicAdversary P)

/-- Both scheme₁ solvers at every known key fit the derived budgets. -/
theorem reductions_within₁ (k : F) :
    dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description generator keyGenerator P.inputWidth
      (P.toGeneral false).solverCode P.goodTime₁
      (Model.LazyAGM.WeightedReduction.goodReductionList Wrapped.terms₁ (Wrapped.wrap₁ k keyGenerator A.view)) ∧
    dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description generator keyGenerator P.inputWidth
      (P.toGeneral false).solverCode P.badTime₁
      (Model.LazyAGM.WeightedReduction.badReductionList Wrapped.terms₁ (Wrapped.wrap₁ k keyGenerator A.view)) :=
  A.reductions_within₁ k

/-- Both scheme₂ solvers at every known key fit the derived budgets. -/
theorem reductions_within₂ (k : F) :
    dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description generator keyGenerator P.inputWidth
      (P.toGeneral false).solverCode P.goodTime₂
      (Model.LazyAGM.WeightedReduction.goodReductionList Wrapped.terms₂ (Wrapped.wrap₂ k keyGenerator A.view)) ∧
    dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description generator keyGenerator P.inputWidth
      (P.toGeneral false).solverCode P.badTime₂
      (Model.LazyAGM.WeightedReduction.badReductionList Wrapped.terms₂ (Wrapped.wrap₂ k keyGenerator A.view)) :=
  A.reductions_within₂ k

/-- Each per-key solver is backend code within its derived budget, at every known key. -/
theorem good₁_reduction_within (k : F) : P.DLogSolverWithin P.goodTime₁ (A.goodReduction₁ k) :=
  (reductions_within₁ P A k).1

theorem bad₁_reduction_within (k : F) : P.DLogSolverWithin P.badTime₁ (A.badReduction₁ k) :=
  (reductions_within₁ P A k).2

theorem good₂_reduction_within (k : F) : P.DLogSolverWithin P.goodTime₂ (A.goodReduction₂ k) :=
  (reductions_within₂ P A k).1

theorem bad₂_reduction_within (k : F) : P.DLogSolverWithin P.badTime₂ (A.badReduction₂ k) :=
  (reductions_within₂ P A k).2

variable [Fintype F] [SampleableType G₁] [Fintype G₁] [DecidableEq Gₜ]

/-- The coefficient game is bounded by the four per-key solvers' successes averaged over the known
key, and the two field losses. -/
theorem security :
    let ε := Model.dlog11Advantage generator keyGenerator
    𝒟[Proofs.lazyGame (Gₜ := Gₜ) generator keyGenerator A.view] {true} ≤
      (∑ k, ε (A.goodReduction₁ k)) / (Fintype.card F : ENNReal) +
      (∑ k, ε (A.badReduction₁ k)) / (Fintype.card F : ENNReal) +
      (∑ k, ε (A.goodReduction₂ k)) / (Fintype.card F : ENNReal) +
      (∑ k, ε (A.badReduction₂ k)) / (Fintype.card F : ENNReal) +
      2 / (Fintype.card F : ENNReal) := by
  intro ε
  have wrapped := Transport.security_wrapped A.view generator keyGenerator P.generates P.pairingInjective
  rw [A.good₁_advantage, A.bad₁_advantage, A.good₂_advantage, A.bad₂_advantage] at wrapped
  exact wrapped

theorem security_of_hardness (ε₁ ε₂ ε₃ ε₄ : ENNReal)
    (h₁ : Model.HardWithin (Model.dlog11Advantage (F := F) generator keyGenerator)
      (dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description generator keyGenerator P.inputWidth
        (P.toGeneral false).solverCode) P.goodTime₁ ε₁)
    (h₂ : Model.HardWithin (Model.dlog11Advantage (F := F) generator keyGenerator)
      (dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description generator keyGenerator P.inputWidth
        (P.toGeneral false).solverCode) P.badTime₁ ε₂)
    (h₃ : Model.HardWithin (Model.dlog11Advantage (F := F) generator keyGenerator)
      (dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description generator keyGenerator P.inputWidth
        (P.toGeneral false).solverCode) P.goodTime₂ ε₃)
    (h₄ : Model.HardWithin (Model.dlog11Advantage (F := F) generator keyGenerator)
      (dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description generator keyGenerator P.inputWidth
        (P.toGeneral false).solverCode) P.badTime₂ ε₄) :
    𝒟[Proofs.lazyGame (Gₜ := Gₜ) generator keyGenerator A.view] {true} ≤
      ε₁ + ε₂ + ε₃ + ε₄ + 2 / (Fintype.card F : ENNReal) :=
  (Transport.security_wrapped A.view generator keyGenerator P.generates P.pairingInjective).trans
    (add_le_add (add_le_add (add_le_add (add_le_add
      (A.good₁_le ε₁ fun k => h₁ _ (reductions_within₁ P A k).1)
      (A.bad₁_le ε₂ fun k => h₂ _ (reductions_within₁ P A k).2))
      (A.good₂_le ε₃ fun k => h₃ _ (reductions_within₂ P A k).1))
      (A.bad₂_le ε₄ fun k => h₄ _ (reductions_within₂ P A k).2)) le_rfl)

end SynchronizedPS.GeneralAGM

namespace SynchronizedPS.GeneralAGM

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasComposition] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]

/-- The public algebraic game at a curve, bounded by the four per-key solvers' DLog successes
averaged over the known key, and two inverse-field-size losses. -/
theorem agm_security (curve : Model.PairingCurve) (securityParameter : Nat) {K M : Type}
    [DecidableEq K] [DecidableEq M]
    (P : Parameters (Q := Q) (F := curve.Scalar securityParameter) (G₁ := curve.SignatureGroup securityParameter)
      (G₂ := curve.KeyGroup securityParameter) (Gₜ := curve.TargetGroup securityParameter) (K := K) (M := M)
      (curve.generator securityParameter) (curve.keyGenerator securityParameter))
    (A : AlgebraicAdversary P) :
    let ε := Model.dlog11Advantage (curve.generator securityParameter) (curve.keyGenerator securityParameter)
    let p := (Fintype.card (curve.Scalar securityParameter) : ENNReal)
    𝒟[Game.agm curve securityParameter A.source] {true} ≤
      (∑ k, ε (A.goodReduction₁ k)) / p + (∑ k, ε (A.badReduction₁ k)) / p +
        (∑ k, ε (A.goodReduction₂ k)) / p + (∑ k, ε (A.badReduction₂ k)) / p + 2 / p :=
  (Game.agm_le curve securityParameter A.source).trans (security P A)

/-- Each of the four per-key solvers is backend code within its derived budget, at every key. -/
theorem agm_good₁_reduction_within (curve : Model.PairingCurve) (securityParameter : Nat) {K M : Type}
    [DecidableEq K] [DecidableEq M]
    (P : Parameters (Q := Q) (F := curve.Scalar securityParameter) (G₁ := curve.SignatureGroup securityParameter)
      (G₂ := curve.KeyGroup securityParameter) (Gₜ := curve.TargetGroup securityParameter) (K := K) (M := M)
      (curve.generator securityParameter) (curve.keyGenerator securityParameter))
    (A : AlgebraicAdversary P) (k : curve.Scalar securityParameter) :
    P.DLogSolverWithin P.goodTime₁ (A.goodReduction₁ k) :=
  good₁_reduction_within P A k

theorem agm_bad₁_reduction_within (curve : Model.PairingCurve) (securityParameter : Nat) {K M : Type}
    [DecidableEq K] [DecidableEq M]
    (P : Parameters (Q := Q) (F := curve.Scalar securityParameter) (G₁ := curve.SignatureGroup securityParameter)
      (G₂ := curve.KeyGroup securityParameter) (Gₜ := curve.TargetGroup securityParameter) (K := K) (M := M)
      (curve.generator securityParameter) (curve.keyGenerator securityParameter))
    (A : AlgebraicAdversary P) (k : curve.Scalar securityParameter) :
    P.DLogSolverWithin P.badTime₁ (A.badReduction₁ k) :=
  bad₁_reduction_within P A k

theorem agm_good₂_reduction_within (curve : Model.PairingCurve) (securityParameter : Nat) {K M : Type}
    [DecidableEq K] [DecidableEq M]
    (P : Parameters (Q := Q) (F := curve.Scalar securityParameter) (G₁ := curve.SignatureGroup securityParameter)
      (G₂ := curve.KeyGroup securityParameter) (Gₜ := curve.TargetGroup securityParameter) (K := K) (M := M)
      (curve.generator securityParameter) (curve.keyGenerator securityParameter))
    (A : AlgebraicAdversary P) (k : curve.Scalar securityParameter) :
    P.DLogSolverWithin P.goodTime₂ (A.goodReduction₂ k) :=
  good₂_reduction_within P A k

theorem agm_bad₂_reduction_within (curve : Model.PairingCurve) (securityParameter : Nat) {K M : Type}
    [DecidableEq K] [DecidableEq M]
    (P : Parameters (Q := Q) (F := curve.Scalar securityParameter) (G₁ := curve.SignatureGroup securityParameter)
      (G₂ := curve.KeyGroup securityParameter) (Gₜ := curve.TargetGroup securityParameter) (K := K) (M := M)
      (curve.generator securityParameter) (curve.keyGenerator securityParameter))
    (A : AlgebraicAdversary P) (k : curve.Scalar securityParameter) :
    P.DLogSolverWithin P.badTime₂ (A.badReduction₂ k) :=
  bad₂_reduction_within P A k

end SynchronizedPS.GeneralAGM
