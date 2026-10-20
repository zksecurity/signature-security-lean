import Signatures.Runtime.Caliper.SchnorrAGMEntryRead
import Signatures.Runtime.BackendSchnorrAGMEntryRead
import Signatures.Runtime.Caliper.SchnorrAGMReachability

/-! Exact source-game connection for the complete Caliper read. The older
native module supplies only tuple definitions here; its abstract program is
not used to implement or certify this Caliper execution. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.EntryRead
open Caliper BoundedSource OracleComp OracleSpec Read
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS : Nat} {M F G I : Type} [Field F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : Layouts w M F G qH qS) (zeroValid : layout.scalar.valid 0)

theorem source_value (sampler : OracleComp spec layout.scalar.Value) (value : (input layout).Value) :
    Subtype.val <$> source layout zeroValid sampler value =
      (fun result => Signatures.Runtime.SchnorrAGM.Native.EntryRead.returnValue (result, value.val.2.2.2)) <$>
        (match cacheMap value.val.2.2.1 value.val.1 with
        | some entry => pure ((entry, value.val.2.2.1), (value.val.2.1, value.val.2.2.2.2.2.2))
        | none => (fun challenge => let fresh := Signatures.Runtime.SchnorrAGM.Native.freshValue (challenge, (value.val.2.1, value.val.2.2.2.2.2.2))
            ((fresh.1, (value.val.1, fresh.1) :: value.val.2.2.1), fresh.2)) <$> (Subtype.val <$> sampler)) := by
  have erased := congrArg
    (fun computation : OracleComp spec ((EncodedEntry F × List ((M × G) × EncodedEntry F)) × ReadStore F) =>
      (fun result => Signatures.Runtime.SchnorrAGM.Native.EntryRead.returnValue (result, value.val.2.2.2)) <$> computation)
    (Cache.source_value layout sampler (packValue layout zeroValid value).1)
  have together := (PFunctor.FreeM.comp_map
    (fun result => Signatures.Runtime.SchnorrAGM.Native.EntryRead.returnValue (result, value.val.2.2.2))
    (fun result : (CacheRead.output layout.cache).Value × (Cache.saved layout).Value => (result.1.val, result.2.val))
    (Cache.source layout sampler (packValue layout zeroValid value).1)).trans erased
  exact (PFunctor.FreeM.comp_map Subtype.val
    (fun result => returnValue layout (result, inputMetadata layout value))
    (Cache.source layout sampler (packValue layout zeroValid value).1)).symm.trans together

/-- Exact equality with the original finite-state read, including its joint
entry/state distribution and the absence of sampling on a cache hit. -/
theorem source_original [SampleableType F] (sampler : ProbComp layout.scalar.Value)
    (uniform : Subtype.val <$> sampler = ($ᵗ F : ProbComp F))
    (s : Signatures.Runtime.SchnorrAGM.State F G M) (key : M × G) (affine : Schnorr.AGM.Affine F)
    (valid : (input layout).valid (key, encodeAffine affine, encodeState s)) :
    Subtype.val <$> source layout zeroValid sampler ⟨(key, encodeAffine affine, encodeState s), valid⟩ =
      (fun result => (encodeEntry result.1, encodeState result.2)) <$> (Signatures.Runtime.SchnorrAGM.readEntry key affine).run s := by
  rw [source_value, uniform]
  change (fun result => Signatures.Runtime.SchnorrAGM.Native.EntryRead.returnValue (result, encodeMetadata s)) <$>
    (match cacheMap (s.cache.map (Prod.map id encodeEntry)) key with
      | some entry => pure ((entry, (encodeState s).1), (encodeAffine affine, s.bad))
      | none => (fun challenge => let fresh := Signatures.Runtime.SchnorrAGM.Native.freshValue (challenge, (encodeAffine affine, s.bad))
          ((fresh.1, (key, fresh.1) :: (encodeState s).1), fresh.2)) <$> ($ᵗ F : ProbComp F)) = _
  rw [cacheMap_encode]
  cases found : cacheMap s.cache key <;>
    simp only [Option.map_none, Option.map_some, Signatures.Runtime.SchnorrAGM.readEntry, StateT.run, found,
      map_pure, bind_pure_comp, Functor.map_map]
  · refine congrArg (fun f => f <$> ($ᵗ F : ProbComp F)) ?_
    funext challenge
    rfl
  · rfl

end Signatures.Runtime.CaliperBackend.SchnorrAGM.EntryRead
