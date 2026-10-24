import Proofs.Proximity.GeneralAGMEncoding
import Proofs.Model.DirectAGM

/-! General implemented algebraic attackers for the original Proximity game.
The source uses function vectors and optional-coordinate indices. Its native
realization uses the equivalent tuple/finite-index representation. Only its own
code, supported execution resources and original-source query counts are supplied;
both reduction certificates are derived separately. -/

open BilinearGroup

open OracleComp OracleSpec PFunctor AlgebraicGroupModel
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM

namespace Proximity.GeneralAGM

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq Gₜ] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]


abbrev Parameters (dimension : Nat) :=
  General.Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (K := K) (M := M) (.proximity dimension)

variable {dimension : Nat}
  (P : Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (K := K) (M := M) dimension)

local instance : DecidableEq ((Index.proximity dimension).messageTy.Value (cryptoBase F G₁ G₂ K M)) :=
  Index.messageValueDecidableEq (.proximity dimension)

/-- A shared AGM attacker and a charged implementation of its derived coefficient
encoding. The caller budget includes regrouping and vector encoding. -/
structure AlgebraicAdversary where
  source : Model.DirectAGM.Adversary F (Option (Fin dimension) × K) ((Fin dimension → F) × K) G₁ G₂
  program : G₂ → OracleComp (generalSpec ((Index.proximity dimension).ty.Value (cryptoBase F G₁ G₂ K M))
    ((Index.proximity dimension).messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ P.randomBound)
    ((AGM.outputTy (Index.proximity dimension).messageTy).Value (cryptoBase F G₁ G₂ K M))
  caller : GeneralCaller.Caller (Q := Q) (bd := P.bd)
  realizes : caller.machine.Implements program
  corresponds : ∀ pk, AGM.outputView <$> simulateQ (generalSource P.randomBound) (program pk) =
    (encodeAdversary (M := M) (Model.DirectAGM.ProofView.adversary P.generator source)).main pk
  runs : caller.RunsWithin (fun _ => P.execution)
  storedCode : P.descriptionSizes.localSize caller.initCode + 2 * P.descriptionSizes.localSize caller.headCode +
    P.descriptionSizes.localSize caller.updateCode ≤ P.callerCodeLimit
  randomQueries : ∀ pk, IsQueryBoundP (source.main (Model.LazyAGM.Interactive.initialInput P.generator pk))
    (fun i => General.queryKind i.value.data = 0) P.queries.random
  hashQueries : ∀ pk, IsQueryBoundP (source.main (Model.LazyAGM.Interactive.initialInput P.generator pk))
    (fun i => General.queryKind i.value.data = 1) P.queries.hash
  signingQueries : ∀ pk, IsQueryBoundP (source.main (Model.LazyAGM.Interactive.initialInput P.generator pk))
    (fun i => General.queryKind i.value.data = 2) P.queries.sign

/-- The original vector/slot proof representation, derived for every shared attacker. -/
def AlgebraicAdversary.proofView (A : AlgebraicAdversary P) :
    Model.LazyAGM.Adversary F (Option (Fin dimension) × K) ((Fin dimension → F) × K) G₁ G₂ :=
  Model.DirectAGM.ProofView.adversary P.generator A.source

def AlgebraicAdversary.native (A : AlgebraicAdversary P) : General.AlgebraicAdversary P where
  source := encodeAdversary (M := M) A.proofView
  program := A.program
  caller := A.caller
  realizes := A.realizes
  corresponds := A.corresponds
  runs := A.runs
  storedCode := A.storedCode
  randomQueries pk := (encodeAdversary_query_bound (M := M) A.proofView pk 0 _).mpr
    (Model.DirectAGM.ProofView.adversary_query_bound _ _ _ _ _ (A.randomQueries pk))
  hashQueries pk := (encodeAdversary_query_bound (M := M) A.proofView pk 1 _).mpr
    (Model.DirectAGM.ProofView.adversary_query_bound _ _ _ _ _ (A.hashQueries pk))
  signingQueries pk := (encodeAdversary_query_bound (M := M) A.proofView pk 2 _).mpr
    (Model.DirectAGM.ProofView.adversary_query_bound _ _ _ _ _ (A.signingQueries pk))

end Proximity.GeneralAGM
