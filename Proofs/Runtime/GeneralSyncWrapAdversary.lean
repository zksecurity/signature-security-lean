import Signatures.SynchronizedPS.GeneralAGMParameters
import Proofs.Runtime.GeneralSyncWrapAverage
import Proofs.Runtime.GeneralWeightedCertificates
import Proofs.Runtime.GeneralCallerResources
import Proofs.BLS.LazyAGMSecurity

/-! # The realized synchronized PS attacker in the general pipeline

One attacker caller, realized in the fixed backend within its own allowances, is wrapped for each
of the two weighted schemes at every known key. Each wrapped caller is a pipeline adversary for
the weighted scheme, so both weighted solvers at every key fit the derived budgets; the four
synchronized PS solvers sample the key, so their advantages are averages of in-budget solvers. -/

open BilinearGroup
open OracleComp OracleSpec PFunctor AlgebraicGroupModel
open PFunctor.DynSystem PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM Signatures.Runtime.WeightedAGM.NativeSolver
open SynchronizedPS.Wrapped (correction₁ correction₂ final₁ final₂ wrap₁ wrap₂ terms₁ terms₂
  solverGood₁ solverBad₁ solverGood₂ solverBad₂)

namespace SynchronizedPS.GeneralAGM

open Signatures.Runtime.SyncWrapGeneral

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]
  {generator : G₁} {keyGenerator : G₂}
  (P : Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (K := K) (M := M) generator keyGenerator)

attribute [local implicit_reducible] PFunctor.Idx

namespace AlgebraicAdversary

variable {P} (A : AlgebraicAdversary P)

/-- The attacker's grouped proof view. -/
abbrev view : Proofs.View F K G₁ G₂ := Proofs.view A.source generator

theorem view_random (pk : G₂ × G₂) :
    IsQueryBoundP (A.view.main pk) (fun i => General.queryKind i = 0) P.innerQueries.random :=
  Model.DirectAGM.ProofView.program_query_bound (A.source.main ⟨(), Model.LazyAGM.Interactive.groupLists [generator] [pk.1, pk.2]⟩) {}
    (fun i => General.queryKind i = 0) _ (A.randomQueries pk)

theorem view_hash (pk : G₂ × G₂) :
    IsQueryBoundP (A.view.main pk) (fun i => General.queryKind i = 1) P.innerQueries.hash :=
  Model.DirectAGM.ProofView.program_query_bound (A.source.main ⟨(), Model.LazyAGM.Interactive.groupLists [generator] [pk.1, pk.2]⟩) {}
    (fun i => General.queryKind i = 1) _ (A.hashQueries pk)

theorem view_sign (pk : G₂ × G₂) :
    IsQueryBoundP (A.view.main pk) (fun i => General.queryKind i = 2) P.innerQueries.sign :=
  Model.DirectAGM.ProofView.program_query_bound (A.source.main ⟨(), Model.LazyAGM.Interactive.groupLists [generator] [pk.1, pk.2]⟩) {}
    (fun i => General.queryKind i = 2) _ (A.signingQueries pk)

/-- The realized program's signing requests are the source's. -/
theorem program_sign (pk : G₂ × G₂) : IsQueryBoundP (A.program pk) isSign P.innerQueries.sign := by
  have h := A.view_sign pk
  rw [← A.corresponds pk, isQueryBoundP_map_iff, isQueryBoundP_map_iff] at h
  have h' := isQueryBoundP_of_simulateQ_generalSource (A.program pk) (fun i => General.queryKind i = 2) _ h
  refine (isQueryBoundP_congr_pred fun i => ?_).1 h'
  rcases i with (n | t) | m <;> simp [rename, General.queryKind, isSign]

/-- Every run of a wrapped caller resolves within the wrapper's budget. -/
theorem resolves (correction finalFn : K × F → F) (keys : G₂ → G₂ × G₂) (pk : G₂) :
    (wrapped correction finalFn keys A.caller).ResolvesIn P.cap ((wrapped correction finalFn keys A.caller).init pk) := by
  have hM := GeneralCaller.implementsWithin_of_resources A.caller P.innerExecution A.runs A.program A.realizes
    P.innerExecution.queries le_rfl
  have h := implementsWithin A.caller.machine correction finalIndex (fin finalFn) keys A.program
    P.innerExecution.queries P.innerQueries.sign hM A.program_sign
  exact ((implementsWithin_iff_implements_and_resolvesIn _ _ _).1 h).2 pk

/-- The attacker wrapped for one weighted scheme at one known key, as a pipeline adversary. -/
def native (b : Bool) (correction finalFn : K × F → F) (keys : G₂ → G₂ × G₂)
    (code : SchemeCode (Q := Q) P.rep correction finalFn keys)
    (scaps : SchemeCaps (Q := Q) P.rep correction finalFn keys code P.wrapWidth P.routineTime)
    (sdesc : SchemeDescriptions P.rep correction finalFn keys code P.descriptionSizes P.routineSize)
    (final : SynchronizedPS.Forgery F K → F) (hfinal : ∀ m, final (m, []) = finalFn m) :
    General.AlgebraicAdversary (P.toGeneral b) where
  source := SynchronizedPS.Wrapped.wrap correction final keys A.view
  program pk := translate correction finalIndex (fin finalFn) (A.program (keys pk)) []
  caller := Signatures.Runtime.SyncWrapGeneral.caller P.rep P.data P.cost P.primitive P.ports P.wports correction finalFn keys code A.caller
  realizes := implements A.caller.machine correction finalIndex (fin finalFn) keys A.program A.realizes
  corresponds pk := decode_translate_eq_wrap correction finalFn A.program A.view A.corresponds final hfinal keys pk
  runs := runsWithin P.innerExecution A.runs P.recovery P.innerRequestWidth (P.caps b code scaps)
    (A.resolves correction finalFn keys)
  storedCode := Signatures.Runtime.SyncWrapGeneral.storedCode P.descriptionSizes P.allowance P.handlerPortSize P.routineSize
    P.instructionSize _ _ _ (P.descriptions code sdesc A.caller) P.innerCodeLimit A.storedCode
  randomQueries pk := by
    rw [SynchronizedPS.Wrapped.wrap_main]
    exact wrapped_random_bound General.queryKind (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) _ _ _ _ _ _ _
      (A.view_random (keys pk))
  hashQueries pk := by
    rw [SynchronizedPS.Wrapped.wrap_main]
    exact wrapped_hash_bound General.queryKind (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) _ _ _ _ _ _ _ _
      (A.view_hash (keys pk)) (A.view_sign (keys pk))
  signingQueries pk := by
    rw [SynchronizedPS.Wrapped.wrap_main]
    exact wrapped_sign_bound General.queryKind (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) _ _ _ _ _ _ _
      (A.view_sign (keys pk))

omit [SampleableType F] [DecidableEq F] [DecidableEq K] in
theorem final₁_nil (k : F) (m : K × F) : final₁ k (m, []) = finalFn₁ k m := by
  simp [final₁, finalFn₁, SynchronizedPS.Reduction.offset]

omit [SampleableType F] [DecidableEq F] [DecidableEq K] in
theorem final₂_nil (k : F) (m : K × F) : final₂ k (m, []) = finalFn₂ k m := by
  simp [final₂, finalFn₂, SynchronizedPS.Reduction.offset]

/-- Scheme₁ (`x•H(t)`, the second key `k` known) at the known key `k`. -/
def native₁ (k : F) : General.AlgebraicAdversary (P.toGeneral false) :=
  A.native false (correction₁ k) (finalFn₁ k) (fun pk => (pk, k • keyGenerator)) (P.scheme₁ k) (P.scheme₁Caps k)
    (P.scheme₁Descriptions k) (final₁ k) (final₁_nil k)

/-- Scheme₂ (`y•(m•H(t))`, the first key `k` known) at the known key `k`. -/
def native₂ (k : F) : General.AlgebraicAdversary (P.toGeneral true) :=
  A.native true (correction₂ k) (finalFn₂ k) (fun pk => (k • keyGenerator, pk)) (P.scheme₂ k) (P.scheme₂Caps k)
    (P.scheme₂Descriptions k) (final₂ k) (final₂_nil k)

theorem terms_false : Index.sourceTerms (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) (P.toGeneral false).cost (.sync false) = terms₁ (F := F) (Period := K) :=
  funext fun m => (Index.sync_sourceTerms _ false m).trans rfl

theorem terms_true : Index.sourceTerms (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) (P.toGeneral true).cost (.sync true) = terms₂ (F := F) (Period := K) :=
  funext fun m => (Index.sync_sourceTerms _ true m).trans rfl

/-! ## The four solvers at every known key fit the derived budgets -/

theorem reductions_within₁ (k : F) :
    dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description generator keyGenerator P.inputWidth
      (P.toGeneral false).solverCode (P.toGeneral false).goodTime
      (Model.LazyAGM.WeightedReduction.goodReductionList terms₁ (wrap₁ k keyGenerator A.view)) ∧
    dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description generator keyGenerator P.inputWidth
      (P.toGeneral false).solverCode (P.toGeneral false).badTime
      (Model.LazyAGM.WeightedReduction.badReductionList terms₁ (wrap₁ k keyGenerator A.view)) := by
  have h := General.reductions_within (P.toGeneral false) (A.native₁ k)
  rw [terms_false] at h
  exact h

theorem reductions_within₂ (k : F) :
    dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description generator keyGenerator P.inputWidth
      (P.toGeneral true).solverCode (P.toGeneral true).goodTime
      (Model.LazyAGM.WeightedReduction.goodReductionList terms₂ (wrap₂ k keyGenerator A.view)) ∧
    dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description generator keyGenerator P.inputWidth
      (P.toGeneral true).solverCode (P.toGeneral true).badTime
      (Model.LazyAGM.WeightedReduction.badReductionList terms₂ (wrap₂ k keyGenerator A.view)) := by
  have h := General.reductions_within (P.toGeneral true) (A.native₂ k)
  rw [terms_true] at h
  exact h

/-! ## The sampled solvers' advantages -/

theorem solverGood₁_eq : Model.dlog11Advantage generator keyGenerator (solverGood₁ A.view) =
    Model.dlog11Advantage generator keyGenerator (fun g X h₂ Y => do
      let k ← ($ᵗ F : ProbComp F)
      Model.LazyAGM.WeightedReduction.goodReductionList terms₁ (wrap₁ k keyGenerator A.view) g X h₂ Y) :=
  BLS.LazyAGM.Reduction.dlog11Advantage_congr generator keyGenerator _ _ fun _ => rfl

theorem solverBad₁_eq : Model.dlog11Advantage generator keyGenerator (solverBad₁ A.view) =
    Model.dlog11Advantage generator keyGenerator (fun g X h₂ Y => do
      let k ← ($ᵗ F : ProbComp F)
      Model.LazyAGM.WeightedReduction.badReductionList terms₁ (wrap₁ k keyGenerator A.view) g X h₂ Y) :=
  BLS.LazyAGM.Reduction.dlog11Advantage_congr generator keyGenerator _ _ fun _ => rfl

theorem solverGood₂_eq : Model.dlog11Advantage generator keyGenerator (solverGood₂ A.view) =
    Model.dlog11Advantage generator keyGenerator (fun g X h₂ Y => do
      let k ← ($ᵗ F : ProbComp F)
      Model.LazyAGM.WeightedReduction.goodReductionList terms₂ (wrap₂ k keyGenerator A.view) g X h₂ Y) :=
  BLS.LazyAGM.Reduction.dlog11Advantage_congr generator keyGenerator _ _ fun _ => rfl

theorem solverBad₂_eq : Model.dlog11Advantage generator keyGenerator (solverBad₂ A.view) =
    Model.dlog11Advantage generator keyGenerator (fun g X h₂ Y => do
      let k ← ($ᵗ F : ProbComp F)
      Model.LazyAGM.WeightedReduction.badReductionList terms₂ (wrap₂ k keyGenerator A.view) g X h₂ Y) :=
  BLS.LazyAGM.Reduction.dlog11Advantage_congr generator keyGenerator _ _ fun _ => rfl

/-- Any bound on every in-budget scheme₁ good solver bounds the sampled one. -/
theorem good₁_le (ε : ENNReal)
    (h : ∀ k, Model.dlog11Advantage generator keyGenerator
      (Model.LazyAGM.WeightedReduction.goodReductionList terms₁ (wrap₁ k keyGenerator A.view)) ≤ ε) :
    Model.dlog11Advantage generator keyGenerator (solverGood₁ A.view) ≤ ε := by
  rw [solverGood₁_eq]
  exact dlog11Advantage_sample_le generator keyGenerator _ ε h

theorem bad₁_le (ε : ENNReal)
    (h : ∀ k, Model.dlog11Advantage generator keyGenerator
      (Model.LazyAGM.WeightedReduction.badReductionList terms₁ (wrap₁ k keyGenerator A.view)) ≤ ε) :
    Model.dlog11Advantage generator keyGenerator (solverBad₁ A.view) ≤ ε := by
  rw [solverBad₁_eq]
  exact dlog11Advantage_sample_le generator keyGenerator _ ε h

theorem good₂_le (ε : ENNReal)
    (h : ∀ k, Model.dlog11Advantage generator keyGenerator
      (Model.LazyAGM.WeightedReduction.goodReductionList terms₂ (wrap₂ k keyGenerator A.view)) ≤ ε) :
    Model.dlog11Advantage generator keyGenerator (solverGood₂ A.view) ≤ ε := by
  rw [solverGood₂_eq]
  exact dlog11Advantage_sample_le generator keyGenerator _ ε h

theorem bad₂_le (ε : ENNReal)
    (h : ∀ k, Model.dlog11Advantage generator keyGenerator
      (Model.LazyAGM.WeightedReduction.badReductionList terms₂ (wrap₂ k keyGenerator A.view)) ≤ ε) :
    Model.dlog11Advantage generator keyGenerator (solverBad₂ A.view) ≤ ε := by
  rw [solverBad₂_eq]
  exact dlog11Advantage_sample_le generator keyGenerator _ ε h

theorem good₁_advantage : Model.dlog11Advantage generator keyGenerator (solverGood₁ A.view) ≤
    (P.toGeneral false).dlogBound (P.toGeneral false).goodTime :=
  A.good₁_le _ fun k => Model.le_advantageBound _ _ _ (A.reductions_within₁ k).1

theorem bad₁_advantage : Model.dlog11Advantage generator keyGenerator (solverBad₁ A.view) ≤
    (P.toGeneral false).dlogBound (P.toGeneral false).badTime :=
  A.bad₁_le _ fun k => Model.le_advantageBound _ _ _ (A.reductions_within₁ k).2

theorem good₂_advantage : Model.dlog11Advantage generator keyGenerator (solverGood₂ A.view) ≤
    (P.toGeneral true).dlogBound (P.toGeneral true).goodTime :=
  A.good₂_le _ fun k => Model.le_advantageBound _ _ _ (A.reductions_within₂ k).1

theorem bad₂_advantage : Model.dlog11Advantage generator keyGenerator (solverBad₂ A.view) ≤
    (P.toGeneral true).dlogBound (P.toGeneral true).badTime :=
  A.bad₂_le _ fun k => Model.le_advantageBound _ _ _ (A.reductions_within₂ k).2

end AlgebraicAdversary

end SynchronizedPS.GeneralAGM
