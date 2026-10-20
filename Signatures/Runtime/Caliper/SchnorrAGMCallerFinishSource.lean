import Signatures.Runtime.Caliper.SchnorrAGMCallerFinish
import Signatures.Runtime.BackendSchnorrAGMInterface

/-! The executed return path erases to the original Schnorr scalar terminal.
Canonical source state is an explicit premise; arbitrary optional-entry padding
is not silently identified with its decode/re-encode normalization. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerFinish
open Caliper BoundedSource OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS : Nat} {M F G : Type} [Field F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    (layout : HashDispatch.Layouts w M F G qH qS) (zeroValid : layout.hash.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 + value.2))
    (sub : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 - value.2))
    (divide : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 / value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)

theorem success_original [SampleableType F] (sampler : ProbComp layout.hash.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampler = ($ᵗ F : ProbComp F))
    (value : Success layout) (valid : admitted layout value)
    (state : Signatures.Runtime.SchnorrAGM.State F G M) (encoded : value.2.val.2 = encodeState state) :
    Subtype.val <$> success layout ⟨0, zeroValid⟩
      (Extraction.source layout zeroValid mul add sub divide mulBuffers addBuffers subBuffers reserve sampler) value =
      Prod.fst <$> (Signatures.Runtime.SchnorrAGM.finishScalar (Interface.decodeForgery value.1.val)).run state := by
  let ready := extractInput layout ⟨value, valid⟩
  have raw : ready.val = ((value.1.val.1.1, value.1.val.2.1, value.1.val.2.2, encodeState state), value.1.val.1.2) := by
    change ((_, _, _, value.2.val.2), _) = _
    rw [encoded]
  have represented : (Extraction.input layout).valid
      ((value.1.val.1.1, value.1.val.2.1, value.1.val.2.2, encodeState state), value.1.val.1.2) := by
    rw [← raw]; exact ready.property
  have same : ready = ⟨((value.1.val.1.1, value.1.val.2.1, value.1.val.2.2, encodeState state), value.1.val.1.2), represented⟩ :=
    Subtype.ext raw
  have core := Extraction.source_original layout zeroValid mul add sub divide mulBuffers addBuffers subBuffers reserve
    sampler uniform state value.1.val.1.1 value.1.val.1.2 value.1.val.2.1 value.1.val.2.2 represented
  have mapped := congrArg (fun computation : ProbComp (F × EncodedState F G M) => Prod.fst <$> computation) core
  rw [success, dite_eq_left valid]
  simp only [Functor.map_map]
  change (fun answer => answer.val.1) <$>
    Extraction.source layout zeroValid mul add sub divide mulBuffers addBuffers subBuffers reserve sampler ready = _
  rw [same]
  simpa only [Functor.map_map, Interface.decodeForgery, Prod.mk.eta] using mapped

end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerFinish
