import Signatures.Runtime.Caliper.SchnorrAGMRead
import Signatures.Runtime.BackendSchnorrAGMRead
import Signatures.Runtime.Caliper.SchnorrAGMReachability

/-! Exact source-game connection for the complete Caliper read. The older
native module supplies only tuple definitions here; its abstract program is
not used to implement or certify this Caliper execution. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Read
open Caliper BoundedSource OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS : Nat} {M F G I : Type} [Field F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : Layouts w M F G qH qS) (zeroValid : layout.scalar.valid 0)

theorem source_value (sampler : OracleComp spec layout.scalar.Value) (value : (input layout).Value) :
    Subtype.val <$> source layout zeroValid sampler value =
      (fun result => Signatures.Runtime.SchnorrAGM.Native.Read.returnValue (result, value.val.2.2.2)) <$>
        (match cacheMap value.val.2.2.1 value.val.1 with
        | some entry => pure ((entry, value.val.2.2.1), (value.val.2.1, value.val.2.2.2.2.2.2))
        | none => (fun challenge => let fresh := Signatures.Runtime.SchnorrAGM.Native.freshValue (challenge, (value.val.2.1, value.val.2.2.2.2.2.2))
            ((fresh.1, (value.val.1, fresh.1) :: value.val.2.2.1), fresh.2)) <$> (Subtype.val <$> sampler)) := by
  have erased := congrArg
    (fun computation : OracleComp spec ((EncodedEntry F × List ((M × G) × EncodedEntry F)) × ReadStore F) =>
      (fun result => Signatures.Runtime.SchnorrAGM.Native.Read.returnValue (result, value.val.2.2.2)) <$> computation)
    (Cache.source_value layout sampler (packValue layout zeroValid value).1)
  have together := (PFunctor.FreeM.comp_map
    (fun result => Signatures.Runtime.SchnorrAGM.Native.Read.returnValue (result, value.val.2.2.2))
    (fun result : (CacheRead.output layout.cache).Value × (Cache.saved layout).Value => (result.1.val, result.2.val))
    (Cache.source layout sampler (packValue layout zeroValid value).1)).trans erased
  exact (PFunctor.FreeM.comp_map Subtype.val
    (fun result => returnValue layout (result, inputMetadata layout value))
    (Cache.source layout sampler (packValue layout zeroValid value).1)).symm.trans together

/-- Exact equality with the original finite-state read, including its joint
challenge/state distribution and the absence of sampling on a cache hit. -/
theorem source_original [SampleableType F] (sampler : ProbComp layout.scalar.Value)
    (uniform : Subtype.val <$> sampler = ($ᵗ F : ProbComp F))
    (s : Signatures.Runtime.SchnorrAGM.State F G M) (key : M × G) (affine : Schnorr.AGM.Affine F)
    (valid : (input layout).valid (key, encodeAffine affine, encodeState s)) :
    Subtype.val <$> source layout zeroValid sampler ⟨(key, encodeAffine affine, encodeState s), valid⟩ =
      (fun result => (result.1, encodeState result.2)) <$> (Signatures.Runtime.SchnorrAGM.read key affine).run s := by
  rw [source_value, uniform]
  change (fun result => Signatures.Runtime.SchnorrAGM.Native.Read.returnValue (result, encodeMetadata s)) <$>
    (match cacheMap (s.cache.map (Prod.map id encodeEntry)) key with
      | some entry => pure ((entry, (encodeState s).1), (encodeAffine affine, s.bad))
      | none => (fun challenge => let fresh := Signatures.Runtime.SchnorrAGM.Native.freshValue (challenge, (encodeAffine affine, s.bad))
          ((fresh.1, (key, fresh.1) :: (encodeState s).1), fresh.2)) <$> ($ᵗ F : ProbComp F)) = _
  rw [cacheMap_encode]
  cases found : cacheMap s.cache key <;>
    simp only [Option.map_none, Option.map_some, Signatures.Runtime.SchnorrAGM.read, StateT.run, found,
      map_pure, bind_pure_comp, Functor.map_map]
  · refine congrArg (fun f => f <$> ($ᵗ F : ProbComp F)) ?_
    funext challenge
    rfl
  · rfl

omit [DecidableEq F] in
/-- The scheme's spare-slot invariant establishes the executable read input;
no enumeration or representation of every possible message is required. -/
theorem input_valid (scalars : ∀ value, layout.scalar.valid value) (points : ∀ value, layout.point.valid value)
    (s : Signatures.Runtime.SchnorrAGM.State F G M) (key : M × G) (affine : Schnorr.AGM.Affine F)
    (keyValid : layout.message.valid key.1) (stateValid : layout.state.valid (encodeState s))
    (spare : s.cache.length ≤ qH + qS) :
    (input layout).valid (key, encodeAffine affine, encodeState s) := by
  refine ⟨⟨⟨keyValid, points _⟩, ⟨scalars _, scalars _⟩, stateValid⟩, ?_⟩
  intro _
  change (s.cache.map (Prod.map id encodeEntry)).length ≤ qH + qS
  simpa only [List.length_map] using spare

omit [DecidableEq F] in
theorem reserved_input (scalars : ∀ value, layout.scalar.valid value) (points : ∀ value, layout.point.valid value)
    {hashes signatures : Nat} {s : Signatures.Runtime.SchnorrAGM.State F G M}
    (room : layout.Reserved hashes signatures s) (key : M × G) (affine : Schnorr.AGM.Affine F)
    (keyValid : layout.message.valid key.1) :
    (input layout).valid (key, encodeAffine affine, encodeState s) :=
  input_valid layout scalars points s key affine keyValid (room.encoded layout scalars points)
    (by have := room.2.1; omega)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Read
