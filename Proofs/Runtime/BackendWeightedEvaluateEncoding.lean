import Proofs.Runtime.BackendWeightedEvaluate
import Proofs.Runtime.WeightedCacheEncoding
import Proofs.LinearFunctional.LazyAGMCache

/-! Native weighted evaluation at the original source indices. In particular,
Proximity uses `Option (Fin ell)` in the source and `Fin (ell + 1)` in code.
The correspondence preserves the entire encountered cache and both accumulators.
These encoding maps are proof relations, not additional runtime operations. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM
open BLS.LazyAGM.Reduction (privateListOracle)

namespace Signatures.Runtime.WeightedAGM.Evaluate

open BackendProgram Read

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M I : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)

/-- Any injective index representation preserves the good evaluator's source law. -/
theorem backendGood_source_encoded [DecidableEq I]
    (encode : I → index.ty.Value (cryptoBase F G₁ G₂ K M)) (hi : Function.Injective encode)
    (rows : List (I × F)) (default : I × F) (cache : List (I × F)) :
    (backendGood rep data cost primitive sampling index).denote
        ((rows.map (Prod.map encode id), Prod.map encode id default, ()), cache.map (Prod.map encode id)) =
      (fun p => (p.1, p.2.map (Prod.map encode id))) <$>
        (simulateQ (privateListOracle (M := I) (R := F)) (evalTerms rows)).run cache := by
  rw [backendGood_source]
  exact evalTerms_encoded encode hi rows cache

/-- Both independent mask coordinates are preserved by the same encoding. -/
theorem backendBad_source_encoded [DecidableEq I]
    (encode : I → index.ty.Value (cryptoBase F G₁ G₂ K M)) (hi : Function.Injective encode)
    (rows : List (I × F)) (default : I × F) (cache : List (I × (F × F))) :
    (backendBad rep data cost primitive sampling index).denote
        ((rows.map (Prod.map encode id), Prod.map encode id default, ()), cache.map (Prod.map encode id)) =
      (fun p => (p.1, p.2.map (Prod.map encode id))) <$>
        (simulateQ (privateListOracle (M := I) (R := F × F)) (evalTerms rows)).run cache := by
  rw [backendBad_source]
  exact evalTerms_encoded encode hi rows cache

theorem proximity_backendGood_source (ell : Nat)
    (rows : List ((Option (Fin ell) × K) × F)) (default : (Option (Fin ell) × K) × F)
    (cache : List ((Option (Fin ell) × K) × F)) :
    (backendGood rep data cost primitive sampling (.proximity ell)).denote
        ((rows.map (Prod.map Weights.encodeProximityKey id), Prod.map Weights.encodeProximityKey id default, ()),
          cache.map (Prod.map Weights.encodeProximityKey id)) =
      (fun p => (p.1, p.2.map (Prod.map Weights.encodeProximityKey id))) <$>
        (simulateQ (privateListOracle (M := Option (Fin ell) × K) (R := F)) (evalTerms rows)).run cache :=
  backendGood_source_encoded rep data cost primitive sampling (.proximity ell)
    Weights.encodeProximityKey (Weights.encodeProximityKey_injective ell) rows default cache

theorem proximity_backendBad_source (ell : Nat)
    (rows : List ((Option (Fin ell) × K) × F)) (default : (Option (Fin ell) × K) × F)
    (cache : List ((Option (Fin ell) × K) × (F × F))) :
    (backendBad rep data cost primitive sampling (.proximity ell)).denote
        ((rows.map (Prod.map Weights.encodeProximityKey id), Prod.map Weights.encodeProximityKey id default, ()),
          cache.map (Prod.map Weights.encodeProximityKey id)) =
      (fun p => (p.1, p.2.map (Prod.map Weights.encodeProximityKey id))) <$>
        (simulateQ (privateListOracle (M := Option (Fin ell) × K) (R := F × F)) (evalTerms rows)).run cache :=
  backendBad_source_encoded rep data cost primitive sampling (.proximity ell)
    Weights.encodeProximityKey (Weights.encodeProximityKey_injective ell) rows default cache

/-- Evaluation of already cached terms returns the exact original cache. -/
theorem backendGood_cached
    (rows : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F))
    (default : index.ty.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F))
    (hc : WeightedReduction.TermsCached rows cache) :
    (backendGood rep data cost primitive sampling index).denote ((rows, default, ()), cache) =
      pure ((rows.map fun p => p.2 • (cache.lookup p.1).getD 0).sum, cache) := by
  rw [backendGood_source, WeightedReduction.evalTerms_cached_eq rows cache hc]

theorem backendBad_cached
    (rows : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F))
    (default : index.ty.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F)))
    (hc : WeightedReduction.TermsCached rows cache) :
    (backendBad rep data cost primitive sampling index).denote ((rows, default, ()), cache) =
      pure ((rows.map fun p => p.2 • (cache.lookup p.1).getD 0).sum, cache) := by
  rw [backendBad_source, WeightedReduction.evalTerms_cached_eq rows cache hc]

end Signatures.Runtime.WeightedAGM.Evaluate
