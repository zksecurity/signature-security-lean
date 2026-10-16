import Signatures.BLS.GeneralAGMFamilyResources

/-! Negligible BLS AGM forgery probability from the actual native reduction
families. The concrete two-branch probability loss is preserved. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.LazyAGM.NativeSolver.Family

namespace BLS.GeneralAGM.Family.Proofs

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)] [∀ n, Fintype (F n)]
  [∀ n, SampleableType (G₁ n)] [∀ n, Fintype (G₁ n)]
  [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G₁ n)] [∀ n, DecidableEq (G₂ n)]
  [∀ n, DecidableEq (Gₜ n)] [∀ n, DecidableEq (M n)]
  [∀ n, AddCommGroup (G₁ n)] [∀ n, Module (F n) (G₁ n)]
  [∀ n, AddCommGroup (G₂ n)] [∀ n, Module (F n) (G₂ n)]
  [∀ n, AddCommGroup (Gₜ n)] [∀ n, Module (F n) (Gₜ n)]
  [∀ n, BilinearGroup.BilinearPairing (F n) (G₁ n) (G₂ n) (Gₜ n)]

theorem security
    (parameters : ∀ n, Parameters (Q := Q) (F := F n) (G₁ := G₁ n) (G₂ := G₂ n) (Gₜ := Gₜ n) (M := M n))
    (config : Configuration.{v, w, x} Q unifSpec)
    (fixed : ∀ n, (parameters n).configuration = config)
    (resources : PolynomialResources parameters)
    (adversary : ∀ n, AlgebraicAdversary (parameters n))
    (hardness : dlogNonuniformHardness config (fun n => (parameters n).rep)
      (fun n => (parameters n).generator) (fun n => (parameters n).keyGenerator)
      (fun n => (parameters n).inputWidth))
    (fieldGrowth : negligible (fun n => 1 / (Fintype.card (F n) : ENNReal))) :
    negligible (fun n => 𝒟[BLS.LazyAGM.game (Gₜ := Gₜ n)
      (parameters n).generator (parameters n).keyGenerator (adversary n).source] {true}) := by
  obtain ⟨goodFits, badFits⟩ := reductions_nonuniform parameters config fixed resources adversary
  have goodSmall := hardness _ goodFits
  have badSmall := hardness _ badFits
  apply negligible_of_le _ (negligible_add (negligible_add goodSmall badSmall) fieldGrowth)
  intro n
  exact BLS.LazyAGM.Reduction.security_arbitrary_messages_list
    (parameters n).generator (parameters n).keyGenerator (adversary n).source
    (parameters n).generates (parameters n).pairingInjective

end BLS.GeneralAGM.Family.Proofs
