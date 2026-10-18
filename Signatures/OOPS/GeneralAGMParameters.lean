import Signatures.Runtime.GeneralWeightedParameters
import Signatures.Model.Proofs.DirectAGM

/-! General implemented algebraic attackers for OOPS. Hash indices contain a
topic and degree; signing inputs contain a scalar and topic. Query counts and
all execution/code limits belong to the fixed resource model. -/

open BilinearGroup

open OracleComp OracleSpec PFunctor AlgebraicGroupModel
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM

namespace OOPS.GeneralAGM

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq Gₜ] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]


abbrev Parameters (degree : Nat) :=
  General.Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (K := K) (M := M) (.oops degree)

variable {degree : Nat}
  (P : Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (K := K) (M := M) degree)

/-- A shared-library source attacker and its bounded backend realization.
The realization produces the internally derived coefficient encoding; its budget
includes this output preparation and regrouping. -/
structure AlgebraicAdversary where
  source : Model.DirectAGM.Adversary F (K × Fin (degree + 1)) (F × K) G₁ G₂
  program : G₂ → OracleComp (generalSpec ((Index.oops degree).ty.Value (cryptoBase F G₁ G₂ K M))
    ((Index.oops degree).messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ P.randomBound)
    ((AGM.outputTy (Index.oops degree).messageTy).Value (cryptoBase F G₁ G₂ K M))
  caller : GeneralCaller.Caller (Q := Q) (bd := P.bd)
  realizes : caller.machine.Implements program
  corresponds : ∀ pk, AGM.outputView <$> simulateQ (generalSource P.randomBound) (program pk) =
    (Model.DirectAGM.ProofView.adversary P.generator source).main pk
  runs : caller.RunsWithin (fun _ => P.execution)
  storedCode : P.descriptionSizes.localSize caller.initCode + 2 * P.descriptionSizes.localSize caller.headCode +
    P.descriptionSizes.localSize caller.updateCode ≤ P.callerCodeLimit
  randomQueries : ∀ pk, IsQueryBoundP (source.main (Model.LazyAGM.Interactive.initialInput P.generator pk))
    (fun i => General.queryKind i.value.data = 0) P.queries.random
  hashQueries : ∀ pk, IsQueryBoundP (source.main (Model.LazyAGM.Interactive.initialInput P.generator pk))
    (fun i => General.queryKind i.value.data = 1) P.queries.hash
  signingQueries : ∀ pk, IsQueryBoundP (source.main (Model.LazyAGM.Interactive.initialInput P.generator pk))
    (fun i => General.queryKind i.value.data = 2) P.queries.sign

def AlgebraicAdversary.proofView (A : AlgebraicAdversary P) :
    Model.LazyAGM.Adversary F (K × Fin (degree + 1)) (F × K) G₁ G₂ :=
  Model.DirectAGM.ProofView.adversary P.generator A.source

def AlgebraicAdversary.native (A : AlgebraicAdversary P) : General.AlgebraicAdversary P where
  source := A.proofView
  program := A.program
  caller := A.caller
  realizes := A.realizes
  corresponds := A.corresponds
  runs := A.runs
  storedCode := A.storedCode
  randomQueries pk := Model.DirectAGM.ProofView.adversary_query_bound _ _ _ _ _ (A.randomQueries pk)
  hashQueries pk := Model.DirectAGM.ProofView.adversary_query_bound _ _ _ _ _ (A.hashQueries pk)
  signingQueries pk := Model.DirectAGM.ProofView.adversary_query_bound _ _ _ _ _ (A.signingQueries pk)

end OOPS.GeneralAGM
