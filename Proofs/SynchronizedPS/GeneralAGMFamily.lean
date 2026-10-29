import Proofs.SynchronizedPS.GeneralAGM
import Proofs.Runtime.GeneralWeightedFamilyResources

/-! Asymptotic synchronized PS security from the general weighted reduction families. The curve may
vary; one fixed backend and polynomial component resources bound the solver code and execution at
every known key. Each sampled solver's advantage is at most that of its best key, a solver family
of the same class, so hardness makes all four negligible. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.WeightedAGM
open Signatures.Runtime.WeightedAGM.NativeSolver.Family

namespace SynchronizedPS.GeneralAGM.Family

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ K M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)]
  [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G₁ n)] [∀ n, DecidableEq (G₂ n)]
  [∀ n, DecidableEq (K n)] [∀ n, DecidableEq (M n)]
  [∀ n, AddCommGroup (G₁ n)] [∀ n, Module (F n) (G₁ n)]
  [∀ n, AddCommGroup (G₂ n)] [∀ n, Module (F n) (G₂ n)]
  [∀ n, AddCommGroup (Gₜ n)] [∀ n, Module (F n) (Gₜ n)]
  [∀ n, BilinearGroup.BilinearPairing (F n) (G₁ n) (G₂ n) (Gₜ n)]

omit [∀ n, SampleableType (F n)] [∀ n, DecidableEq (F n)] in
/-- A key maximizing a solver family's advantage at every security parameter. -/
theorem exists_best [∀ n, Fintype (F n)] (adv : ∀ n, F n → ENNReal) : ∃ k : ∀ n, F n, ∀ n x, adv n x ≤ adv n (k n) := by
  have h : ∀ n, ∃ k : F n, ∀ x, adv n x ≤ adv n k := fun n => by
    obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (adv n) (Finset.univ_nonempty_iff.mpr ⟨0⟩)
    exact ⟨k, fun x => hk x (Finset.mem_univ x)⟩
  choose k hk using h
  exact ⟨k, hk⟩

variable {generator : ∀ n, G₁ n} {keyGenerator : ∀ n, G₂ n}
  (parameters : ∀ n, Parameters (Q := Q) (F := F n) (G₁ := G₁ n) (G₂ := G₂ n)
    (Gₜ := Gₜ n) (K := K n) (M := M n) (generator n) (keyGenerator n))
  (config : Configuration.{v, w, x} Q unifSpec)
  (fixed : Family.Fixed parameters config)
  (resources : Family.PolynomialResources parameters)
  (adversary : ∀ n, AlgebraicAdversary (parameters n))

include fixed in
/-- The pipeline parameters of the two schemes share every resource. -/
theorem fixed_true : ∀ n, ((parameters n).toGeneral true).configuration = config := fixed

include resources in
theorem resources_true : General.Family.PolynomialResources (fun n => (parameters n).toGeneral true) :=
  ⟨resources.degree, resources.overhead, resources.work, resources.randomQueries, resources.hashQueries,
    resources.signingQueries, resources.inputWidth, resources.width, resources.outputWidth, resources.routeWidth,
    resources.comparisonTime, resources.scalarTime, resources.opTime, resources.handlerAdapterTime,
    resources.solverAdapterTime, resources.dynamicTime, resources.handlerTickTime, resources.callerTickTime,
    resources.extractionTickTime, resources.callerCode, resources.scalarCode, resources.dynamicCode,
    resources.structuralCode, resources.instructionCode, resources.handlerCode, resources.solverPortCode⟩

include fixed resources

/-- At any choice of known keys, all four wrapped solver families are nonuniform solvers of the
fixed class. -/
theorem reductions_nonuniform (k₁ k₂ k₃ k₄ : ∀ n, F n) :
    dlogNonuniformWithin config (fun n => (parameters n).rep) generator keyGenerator (fun n => (parameters n).inputWidth)
      (fun n => Model.LazyAGM.WeightedReduction.goodReductionList Wrapped.terms₁
        (Wrapped.wrap₁ (k₁ n) (keyGenerator n) (adversary n).view)) ∧
    dlogNonuniformWithin config (fun n => (parameters n).rep) generator keyGenerator (fun n => (parameters n).inputWidth)
      (fun n => Model.LazyAGM.WeightedReduction.badReductionList Wrapped.terms₁
        (Wrapped.wrap₁ (k₂ n) (keyGenerator n) (adversary n).view)) ∧
    dlogNonuniformWithin config (fun n => (parameters n).rep) generator keyGenerator (fun n => (parameters n).inputWidth)
      (fun n => Model.LazyAGM.WeightedReduction.goodReductionList Wrapped.terms₂
        (Wrapped.wrap₂ (k₃ n) (keyGenerator n) (adversary n).view)) ∧
    dlogNonuniformWithin config (fun n => (parameters n).rep) generator keyGenerator (fun n => (parameters n).inputWidth)
      (fun n => Model.LazyAGM.WeightedReduction.badReductionList Wrapped.terms₂
        (Wrapped.wrap₂ (k₄ n) (keyGenerator n) (adversary n).view)) :=
  ⟨General.Family.solver_nonuniform (fun n => (parameters n).toGeneral false) config fixed resources _ _
      resources.goodTime (fun n => (reductions_within₁ (parameters n) (adversary n) (k₁ n)).1),
    General.Family.solver_nonuniform (fun n => (parameters n).toGeneral false) config fixed resources _ _
      resources.badTime (fun n => (reductions_within₁ (parameters n) (adversary n) (k₂ n)).2),
    General.Family.solver_nonuniform (fun n => (parameters n).toGeneral true) config (fixed_true parameters config fixed)
      (resources_true parameters resources) _ _ (resources_true parameters resources).goodTime
      (fun n => (reductions_within₂ (parameters n) (adversary n) (k₃ n)).1),
    General.Family.solver_nonuniform (fun n => (parameters n).toGeneral true) config (fixed_true parameters config fixed)
      (resources_true parameters resources) _ _ (resources_true parameters resources).badTime
      (fun n => (reductions_within₂ (parameters n) (adversary n) (k₄ n)).2)⟩

variable [∀ n, Fintype (F n)] [∀ n, SampleableType (G₁ n)] [∀ n, Fintype (G₁ n)] [∀ n, DecidableEq (Gₜ n)]
  (hardness : Family.dlogHardness parameters config)
  (fieldGrowth : negligible (fun n => 1 / (Fintype.card (F n) : ENNReal)))

include hardness fieldGrowth

theorem Proofs.security :
    negligible (fun n => 𝒟[SynchronizedPS.Proofs.lazyGame (Gₜ := Gₜ n) (generator n) (keyGenerator n)
      (adversary n).view] {true}) := by
  obtain ⟨k₁, hk₁⟩ := exists_best (F := F) fun n x => Model.dlog11Advantage (generator n) (keyGenerator n)
    (Model.LazyAGM.WeightedReduction.goodReductionList Wrapped.terms₁ (Wrapped.wrap₁ x (keyGenerator n) (adversary n).view))
  obtain ⟨k₂, hk₂⟩ := exists_best (F := F) fun n x => Model.dlog11Advantage (generator n) (keyGenerator n)
    (Model.LazyAGM.WeightedReduction.badReductionList Wrapped.terms₁ (Wrapped.wrap₁ x (keyGenerator n) (adversary n).view))
  obtain ⟨k₃, hk₃⟩ := exists_best (F := F) fun n x => Model.dlog11Advantage (generator n) (keyGenerator n)
    (Model.LazyAGM.WeightedReduction.goodReductionList Wrapped.terms₂ (Wrapped.wrap₂ x (keyGenerator n) (adversary n).view))
  obtain ⟨k₄, hk₄⟩ := exists_best (F := F) fun n x => Model.dlog11Advantage (generator n) (keyGenerator n)
    (Model.LazyAGM.WeightedReduction.badReductionList Wrapped.terms₂ (Wrapped.wrap₂ x (keyGenerator n) (adversary n).view))
  obtain ⟨good₁, bad₁, good₂, bad₂⟩ := reductions_nonuniform parameters config fixed resources adversary k₁ k₂ k₃ k₄
  have small₁ := hardness _ good₁
  have small₂ := hardness _ bad₁
  have small₃ := hardness _ good₂
  have small₄ := hardness _ bad₂
  apply negligible_of_le _ (negligible_add (negligible_add (negligible_add (negligible_add small₁ small₂) small₃) small₄)
    (negligible_add fieldGrowth fieldGrowth))
  intro n
  have two : (2 : ENNReal) / (Fintype.card (F n) : ENNReal) =
      1 / (Fintype.card (F n) : ENNReal) + 1 / (Fintype.card (F n) : ENNReal) := by
    rw [ENNReal.div_add_div_same, one_add_one_eq_two]
  have bound := (Transport.security_wrapped (Gₜ := Gₜ n) (adversary n).view (generator n) (keyGenerator n)
    (parameters n).generates (parameters n).pairingInjective).trans
    (add_le_add (add_le_add (add_le_add (add_le_add
      ((adversary n).good₁_le _ (hk₁ n)) ((adversary n).bad₁_le _ (hk₂ n)))
      ((adversary n).good₂_le _ (hk₃ n))) ((adversary n).bad₂_le _ (hk₄ n))) le_rfl)
  rw [two] at bound
  simpa only [Pi.add_apply] using bound

end SynchronizedPS.GeneralAGM.Family
