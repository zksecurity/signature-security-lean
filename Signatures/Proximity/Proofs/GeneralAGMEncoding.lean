import Signatures.Runtime.GeneralWeightedParameters
import Signatures.LinearFunctional.Proofs.LazyAGMTransport

/-! The native tuple and finite-coordinate interface represents Proximity's
original vector and optional-coordinate interface exactly. Renaming preserves
all three query counts and both whole DLog reductions. These maps describe the
representation relation; runtime work is charged to the actual native caller. -/

open OracleComp OracleSpec Model.LazyAGM
open Model.LazyAGM.WeightedReduction Model.LazyAGM.WeightedTransport
open Signatures.Runtime Signatures.Runtime.WeightedAGM

namespace Signatures.Runtime.WeightedAGM.General

theorem mapMain_query_bound {F I J N M G₁ : Type} (index : I → J) (message : N → M)
    (program : OracleComp (advSpec I N G₁) (Output F N)) (kind : Fin 3) (count : Nat) :
    IsQueryBoundP (mapMain index message program) (fun q => queryKind q = kind) count ↔
      IsQueryBoundP program (fun q => queryKind q = kind) count := by
  induction program using OracleComp.inductionOn generalizing count with
  | pure out => simp [mapMain]
  | query_bind q next ih =>
      change IsQueryBoundP
        (mapMain index message (show OracleComp (advSpec I N G₁) (Output F N) from query q >>= next)) _ _ ↔ _
      rw [mapMain_query_bind]
      rcases q with ((n | i) | m) <;> simp only [queries, HasQuery.instOfMonadLift_query] <;>
        rw [isQueryBoundP_query_bind_iff (spec := advSpec J M G₁),
          isQueryBoundP_query_bind_iff (spec := advSpec I N G₁)] <;>
        exact and_congr Iff.rfl (forall_congr' fun r => ih r _)

end Signatures.Runtime.WeightedAGM.General

namespace Proximity.GeneralAGM

variable {F G₁ G₂ K M : Type} {ell : Nat}

def encodeAdversary
    (A : Adversary F (Option (Fin ell) × K) ((Fin ell → F) × K) G₁ G₂) :
    Adversary F ((Index.proximity ell).ty.Value (cryptoBase F G₁ G₂ K M))
      ((Index.proximity ell).messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ G₂ :=
  mapAdversary Weights.encodeProximityKey
    (Weights.proximityMessageEquiv (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) ell).symm A

theorem encodeAdversary_query_bound
    (A : Adversary F (Option (Fin ell) × K) ((Fin ell → F) × K) G₁ G₂)
    (pk : G₂) (kind : Fin 3) (count : Nat) :
    IsQueryBoundP ((encodeAdversary (M := M) A).main pk) (fun q => General.queryKind q = kind) count ↔
      IsQueryBoundP (A.main pk) (fun q => General.queryKind q = kind) count :=
  General.mapMain_query_bound _ _ _ _ _

variable [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

omit [SampleableType F] in
theorem encoded_terms (cost : PrimitiveCosts) (message : (Fin ell → F) × K) :
    Index.sourceTerms cost (.proximity ell)
        ((Weights.proximityMessageEquiv (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) ell).symm message) =
      (Proximity.LazyAGM.terms message).map (Prod.map Weights.encodeProximityKey id) := by
  rw [Index.proximity_sourceTerms, Equiv.apply_symm_apply]

theorem goodReduction_encoded (cost : PrimitiveCosts)
    (A : Adversary F (Option (Fin ell) × K) ((Fin ell → F) × K) G₁ G₂) :
    goodReductionList (Index.sourceTerms cost (.proximity ell)) (encodeAdversary (M := M) A) =
      goodReductionList Proximity.LazyAGM.terms A :=
  goodReduction_map Weights.encodeProximityKey (Weights.encodeProximityKey_injective ell)
    _ _ _ (encoded_terms cost) A

theorem badReduction_encoded (cost : PrimitiveCosts)
    (A : Adversary F (Option (Fin ell) × K) ((Fin ell → F) × K) G₁ G₂) :
    badReductionList (Index.sourceTerms cost (.proximity ell)) (encodeAdversary (M := M) A) =
      badReductionList Proximity.LazyAGM.terms A :=
  badReduction_map Weights.encodeProximityKey (Weights.encodeProximityKey_injective ell)
    _ _ _ (encoded_terms cost) A

end Proximity.GeneralAGM
