import Proofs.Runtime.Caliper.SchnorrAGMExtraction
import Proofs.Runtime.Caliper.SchnorrAGMHashDispatchSource

/-! Exact final-forgery correspondence with the original Schnorr scalar
terminal, including malformed shapes and the complete updated private state. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Extraction
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

theorem prepared_original [SampleableType F] (sampler : ProbComp layout.hash.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampler = ($ᵗ F : ProbComp F))
    (state : Signatures.Runtime.SchnorrAGM.State F G M) (key : M × G) (coefficients : List F)
    (valid : layout.hash.input.valid (key, coefficients, encodeState state)) :
    Subtype.val <$> EntryRead.source layout.hash.scheme zeroValid sampler
      (Hash.prepareValue layout.hash zeroValid mul add mulBuffers addBuffers reserve ⟨(key, coefficients, encodeState state), valid⟩) =
      (fun result => (encodeEntry result.1, encodeState result.2)) <$>
        (Signatures.Runtime.SchnorrAGM.readEntry key (Schnorr.AGM.flatten coefficients state.representations)).run state := by
  let ready := Hash.prepareValue layout.hash zeroValid mul add mulBuffers addBuffers reserve ⟨(key, coefficients, encodeState state), valid⟩
  have value : ready.val = (key, encodeAffine (Schnorr.AGM.flatten coefficients state.representations), encodeState state) := by
    change (key, Flatten.denote (state.representations.map encodeAffine, coefficients), encodeState state) = _
    rw [Flatten.denote_source]
  have admitted : (Read.input layout.hash.scheme).valid
      (key, encodeAffine (Schnorr.AGM.flatten coefficients state.representations), encodeState state) := by
    rw [← value]
    exact ready.property
  have same : ready = ⟨(key, encodeAffine (Schnorr.AGM.flatten coefficients state.representations), encodeState state), admitted⟩ :=
    Subtype.ext value
  change Subtype.val <$> EntryRead.source layout.hash.scheme zeroValid sampler ready = _
  rw [same]
  exact EntryRead.source_original layout.hash.scheme zeroValid sampler uniform state key _ admitted

theorem source_no (sampler : ProbComp layout.hash.scheme.scalar.Value)
    (value : (input layout).Value) (invalid : HashDispatch.shape value.val.1 = false) :
    Subtype.val <$> source layout zeroValid mul add sub divide mulBuffers addBuffers subBuffers reserve sampler value =
      pure (0, value.val.1.2.2.2) := by
  unfold source
  rw [ExtractionEntry.source_no layout zeroValid mul add mulBuffers addBuffers reserve sampler (request layout value) invalid]
  simp only [map_pure]
  rfl

theorem source_original [SampleableType F] (sampler : ProbComp layout.hash.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampler = ($ᵗ F : ProbComp F))
    (state : Signatures.Runtime.SchnorrAGM.State F G M) (message : M) (z : F) (groups : List G) (rows : List (List F))
    (valid : (input layout).valid ((message, groups, rows, encodeState state), z)) :
    Subtype.val <$> source layout zeroValid mul add sub divide mulBuffers addBuffers subBuffers reserve sampler
      ⟨((message, groups, rows, encodeState state), z), valid⟩ =
      (fun result => (result.1, encodeState result.2)) <$>
        (Signatures.Runtime.SchnorrAGM.finishScalar ⟨⟨(message, z), fun _ => groups⟩, fun _ => rows⟩).run state := by
  rcases groups with _ | ⟨point, _ | ⟨other, rest⟩⟩
  · rw [source_no layout zeroValid mul add sub divide mulBuffers addBuffers subBuffers reserve sampler _ (by simp [HashDispatch.shape])]
    simp only [Signatures.Runtime.SchnorrAGM.finishScalar, StateT.run_pure, map_pure]
  · rcases rows with _ | ⟨coefficients, _ | ⟨other, rest⟩⟩
    · rw [source_no layout zeroValid mul add sub divide mulBuffers addBuffers subBuffers reserve sampler _ (by simp [HashDispatch.shape])]
      simp only [Signatures.Runtime.SchnorrAGM.finishScalar, StateT.run_pure, map_pure]
    · have shaped : HashDispatch.shape (message, [point], [coefficients], encodeState state) = true := by simp [HashDispatch.shape]
      unfold source
      rw [ExtractionEntry.source_yes layout zeroValid mul add mulBuffers addBuffers reserve sampler _ shaped]
      have core := prepared_original layout zeroValid mul add mulBuffers addBuffers reserve sampler uniform state
        (message, point) coefficients (layout.acceptedValue ⟨(message, [point], [coefficients], encodeState state), valid.1, shaped⟩).property
      have mapped := congrArg
        (fun computation : ProbComp (EncodedEntry F × EncodedState F G M) =>
          (fun result => (ExtractionArithmetic.value (result.1, z), result.2)) <$> computation) core
      simpa only [Functor.map_map, ExtractionRead.solution, ExtractionRead.arguments, response,
        ExtractionArithmetic.value_encode, Signatures.Runtime.SchnorrAGM.finishScalar, StateT.run_bind,
        StateT.run_get, StateT.run_pure, StateT.run_map, pure_bind, bind_pure_comp, request,
        HashDispatch.Layouts.acceptedValue, HashDispatch.Layouts.point, HashDispatch.Layouts.row,
        List.getElem_cons_zero] using mapped
    · rw [source_no layout zeroValid mul add sub divide mulBuffers addBuffers subBuffers reserve sampler _ (by simp [HashDispatch.shape])]
      simp only [Signatures.Runtime.SchnorrAGM.finishScalar, StateT.run_pure, map_pure]
  · rw [source_no layout zeroValid mul add sub divide mulBuffers addBuffers subBuffers reserve sampler _ (by simp [HashDispatch.shape])]
    simp only [Signatures.Runtime.SchnorrAGM.finishScalar, StateT.run_pure, map_pure]

omit [DecidableEq F] in
theorem reserved_input (scalars : ∀ value, layout.hash.scheme.scalar.valid value) (points : ∀ value, layout.hash.scheme.point.valid value)
    {hashes signatures : Nat} {state : Signatures.Runtime.SchnorrAGM.State F G M}
    (room : layout.hash.scheme.Reserved hashes signatures state) (message : M) (z : F) (groups : List G) (rows : List (List F))
    (messageValid : layout.hash.scheme.message.valid message) (groupLength : groups.length ≤ layout.groups)
    (rowLength : rows.length ≤ layout.rows) (coefficientLengths : ∀ row ∈ rows, row.length ≤ layout.hash.coefficients) :
    (input layout).valid ((message, groups, rows, encodeState state), z) :=
  ⟨HashDispatch.reserved_input layout scalars points room message groups rows messageValid groupLength rowLength coefficientLengths, scalars z⟩

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Extraction
