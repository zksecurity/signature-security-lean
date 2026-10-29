import Proofs.Runtime.GeneralSyncWrapParameters
import Proofs.Runtime.GeneralWeightedFamilyResources

/-! General implemented algebraic attackers for synchronized PS. The attacker supplies one caller
realized in the fixed backend at the single-signer interface, within its own query, execution and
stored-code allowances; the two weighted schemes' routines at every known key and the pipeline's
components are the model. All four reduction budgets are derived. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.WeightedAGM
open Signatures.Runtime.SyncWrapGeneral (Spec OutTy embed decode)

namespace SynchronizedPS.GeneralAGM

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]

/-- One fixed backend, the attacker's interface and allowances, and the two schemes' routines. -/
abbrev Parameters (generator : G₁) (keyGenerator : G₂) :=
  SyncWrapGeneral.Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (K := K) (M := M) generator keyGenerator

variable {generator : G₁} {keyGenerator : G₂}
  (P : Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (K := K) (M := M) generator keyGenerator)

/-- A source attacker of the public game with its backend realization: the realized caller at the
attacker's own interface, within its own query, execution and stored-code allowances. -/
structure AlgebraicAdversary where
  source : Reduction.Adversary F K G₁ G₂
  program : G₂ × G₂ → OracleComp (Spec F K G₁ P.randomBound) (OutTy.Value (cryptoBase F G₁ G₂ K M))
  caller : GeneralCaller.Caller (Q := Q) (bd := P.bdI)
  realizes : caller.machine.Implements program
  corresponds : ∀ pk, embed <$> (decode F K G₁ G₂ M <$> simulateQ (generalSource P.randomBound) (program pk)) =
    (Proofs.view source generator).main pk
  runs : caller.RunsWithin (fun _ => P.innerExecution)
  storedCode : P.descriptionSizes.localSize caller.initCode + 2 * P.descriptionSizes.localSize caller.headCode +
    P.descriptionSizes.localSize caller.updateCode ≤ P.innerCodeLimit
  randomQueries : ∀ pk : G₂ × G₂, IsQueryBoundP
    (source.main ⟨(), Model.LazyAGM.Interactive.groupLists [generator] [pk.1, pk.2]⟩)
    (fun i => General.queryKind i.value.data = 0) P.innerQueries.random
  hashQueries : ∀ pk : G₂ × G₂, IsQueryBoundP
    (source.main ⟨(), Model.LazyAGM.Interactive.groupLists [generator] [pk.1, pk.2]⟩)
    (fun i => General.queryKind i.value.data = 1) P.innerQueries.hash
  signingQueries : ∀ pk : G₂ × G₂, IsQueryBoundP
    (source.main ⟨(), Model.LazyAGM.Interactive.groupLists [generator] [pk.1, pk.2]⟩)
    (fun i => General.queryKind i.value.data = 2) P.innerQueries.sign

namespace Parameters

/-- The derived runtimes of the four complete reductions. -/
def goodTime₁ : Nat := (P.toGeneral false).goodTime
def badTime₁ : Nat := (P.toGeneral false).badTime
def goodTime₂ : Nat := (P.toGeneral true).goodTime
def badTime₂ : Nat := (P.toGeneral true).badTime

/-- Supremum of `(1,1)`-DLog success over solvers of the fixed backend within the derived stored
code, the pipeline's input width and the given time. The two schemes share the class. -/
noncomputable def dlogBound (time : Nat) : ENNReal := (P.toGeneral false).dlogBound time

/-- The four reduction branches plus the original two inverse-field-size losses. -/
noncomputable def securityBound [Fintype F] : ENNReal :=
  P.dlogBound P.goodTime₁ + P.dlogBound P.badTime₁ + P.dlogBound P.goodTime₂ + P.dlogBound P.badTime₂ +
    2 / (Fintype.card F : ENNReal)

end Parameters

namespace Family

open Signatures.Runtime.WeightedAGM.NativeSolver.Family

variable {F G₁ G₂ Gₜ K M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)]
  [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G₁ n)] [∀ n, DecidableEq (G₂ n)]
  [∀ n, DecidableEq (K n)] [∀ n, DecidableEq (M n)]
  [∀ n, AddCommGroup (G₁ n)] [∀ n, Module (F n) (G₁ n)]
  [∀ n, AddCommGroup (G₂ n)] [∀ n, Module (F n) (G₂ n)]
  [∀ n, AddCommGroup (Gₜ n)] [∀ n, Module (F n) (Gₜ n)]
  [∀ n, BilinearGroup.BilinearPairing (F n) (G₁ n) (G₂ n) (Gₜ n)]
  {generator : ∀ n, G₁ n} {keyGenerator : ∀ n, G₂ n}
  (parameters : ∀ n, Parameters (Q := Q) (F := F n) (G₁ := G₁ n) (G₂ := G₂ n)
    (Gₜ := Gₜ n) (K := K n) (M := M n) (generator n) (keyGenerator n))
  (config : Configuration.{v, w, x} Q unifSpec)

/-- One backend configuration across the family. -/
abbrev Fixed : Prop := ∀ n, ((parameters n).toGeneral false).configuration = config

/-- Polynomial component allowances; complete solver times and code are derived. -/
abbrev PolynomialResources : Prop :=
  General.Family.PolynomialResources (fun n => (parameters n).toGeneral false)

/-- Nonuniform `(1,1)`-DLog hardness for solver families of the fixed backend at the pipeline's
input width. -/
abbrev dlogHardness : Prop :=
  dlogNonuniformHardness config (fun n => (parameters n).rep) generator keyGenerator (fun n => (parameters n).inputWidth)

end Family

end SynchronizedPS.GeneralAGM
