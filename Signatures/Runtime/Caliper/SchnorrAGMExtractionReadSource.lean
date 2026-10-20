import Signatures.Runtime.Caliper.SchnorrAGMExtractionRead

/-! Exact joint scalar/state correspondence with the terminal source read.
Extraction uses the returned first cached entry, including its optional affine
explanation. The source state's newly raised bad flag is preserved. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.ExtractionRead
open Caliper BoundedSource OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS : Nat} {M F G : Type} [Field F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    (layout : Layouts w M F G qH qS) (zeroValid : layout.scalar.valid 0)
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    (sub : Implementation .unit layout.affine layout.scalar (fun value => value.1 - value.2))
    (divide : Implementation .unit layout.affine layout.scalar (fun value => value.1 / value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w)

theorem source_original [SampleableType F] (sampler : ProbComp layout.scalar.Value)
    (uniform : Subtype.val <$> sampler = ($ᵗ F : ProbComp F))
    (state : Signatures.Runtime.SchnorrAGM.State F G M) (key : M × G) (affine : Schnorr.AGM.Affine F) (z : F)
    (valid : (input layout).valid ((key, encodeAffine affine, encodeState state), z)) :
    Subtype.val <$> source layout zeroValid add sub divide addBuffers subBuffers reserve sampler
      ⟨((key, encodeAffine affine, encodeState state), z), valid⟩ =
      (fun result => (Signatures.Runtime.SchnorrAGM.entrySolution z result.1, encodeState result.2)) <$>
        (Signatures.Runtime.SchnorrAGM.readEntry key affine).run state := by
  have entry := EntryRead.source_original layout zeroValid sampler uniform state key affine valid.1
  have mapped := congrArg
    (fun computation : ProbComp (EncodedEntry F × EncodedState F G M) =>
      (fun result => (ExtractionArithmetic.value (result.1, z), result.2)) <$> computation) entry
  simpa only [source, Functor.map_map, solution, arguments, response, readInput, ExtractionArithmetic.value_encode] using mapped

end Signatures.Runtime.CaliperBackend.SchnorrAGM.ExtractionRead
