import Proofs.Runtime.Caliper.SchnorrAGMHashDispatch
import Proofs.Runtime.SchnorrAGMExecution

/-! The all-shape Caliper hash dispatcher has exactly the original Schnorr
handler's reply and state law, including rejection without a random query. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.HashDispatch
open Caliper BoundedSource OracleComp OracleSpec Schnorr.AGM
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS : Nat} {M F G : Type} [Field F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    (layout : Layouts w M F G qH qS) (zeroValid : layout.hash.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

theorem source_original [AddCommGroup G] [Module F G] [SampleableType F]
    (sampler : ProbComp layout.hash.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampler = ($ᵗ F : ProbComp F))
    (g pk : G) (state : Signatures.Runtime.SchnorrAGM.State F G M) (message : M) (groups : List G) (rows : List (List F))
    (valid : layout.input.valid (message, groups, rows, encodeState state)) :
    (fun value => (scalarReply (G := G) value.val.1, value.val.2)) <$>
      source layout zeroValid mul add mulBuffers addBuffers reserve sampler ⟨(message, groups, rows, encodeState state), valid⟩ =
      (fun result => (result.1, encodeState result.2)) <$>
        (Signatures.Runtime.SchnorrAGM.handler g pk ⟨⟨.hash message, fun _ => groups⟩, fun _ => rows⟩).run state := by
  rcases groups with _ | ⟨point, _ | ⟨other, rest⟩⟩
  · rw [source_no layout zeroValid mul add mulBuffers addBuffers reserve sampler _ (by simp [shape])]
    simp only [map_pure, Signatures.Runtime.SchnorrAGM.handler, StateT.run]
    rfl
  · rcases rows with _ | ⟨coefficients, _ | ⟨other, rest⟩⟩
    · rw [source_no layout zeroValid mul add mulBuffers addBuffers reserve sampler _ (by simp [shape])]
      simp only [map_pure, Signatures.Runtime.SchnorrAGM.handler, StateT.run]
      rfl
    · have shaped : shape (message, [point], [coefficients], encodeState state) = true := by simp [shape]
      rw [source_yes layout zeroValid mul add mulBuffers addBuffers reserve sampler _ shaped]
      have core := Hash.source_original layout.hash zeroValid mul add mulBuffers addBuffers reserve sampler uniform state
        (message, point) coefficients (layout.acceptedValue ⟨(message, [point], [coefficients], encodeState state), valid, shaped⟩).property
      have lifted := congrArg
        (fun computation : ProbComp (F × EncodedState F G M) => (fun result => (scalarReply (G := G) result.1, result.2)) <$> computation) core
      simp only [Functor.map_map, Signatures.Runtime.SchnorrAGM.handler, StateT.run, bind_pure_comp] at lifted ⊢
      exact lifted
    · rw [source_no layout zeroValid mul add mulBuffers addBuffers reserve sampler _ (by simp [shape])]
      simp only [map_pure, Signatures.Runtime.SchnorrAGM.handler, StateT.run]
      rfl
  · rw [source_no layout zeroValid mul add mulBuffers addBuffers reserve sampler _ (by simp [shape])]
    simp only [map_pure, Signatures.Runtime.SchnorrAGM.handler, StateT.run]
    rfl

omit [DecidableEq F] in
theorem input_valid (scalars : ∀ value, layout.hash.scheme.scalar.valid value) (points : ∀ value, layout.hash.scheme.point.valid value)
    (state : Signatures.Runtime.SchnorrAGM.State F G M) (message : M) (groups : List G) (rows : List (List F))
    (messageValid : layout.hash.scheme.message.valid message) (groupLength : groups.length ≤ layout.groups)
    (rowLength : rows.length ≤ layout.rows) (coefficientLengths : ∀ row ∈ rows, row.length ≤ layout.hash.coefficients)
    (stateValid : layout.hash.scheme.state.valid (encodeState state)) (spare : state.cache.length ≤ qH + qS) :
    layout.input.valid (message, groups, rows, encodeState state) := by
  refine ⟨⟨messageValid, ⟨groupLength, fun point _ => points point⟩,
    ⟨rowLength, fun row member => ⟨coefficientLengths row member, fun scalar _ => scalars scalar⟩⟩, stateValid⟩, ?_⟩
  unfold Layouts.admissible
  split
  · intro _
    simpa only [encodeState, List.length_map] using spare
  · trivial

omit [DecidableEq F] in
theorem reserved_input (scalars : ∀ value, layout.hash.scheme.scalar.valid value) (points : ∀ value, layout.hash.scheme.point.valid value)
    {hashes signatures : Nat} {state : Signatures.Runtime.SchnorrAGM.State F G M}
    (room : layout.hash.scheme.Reserved hashes signatures state) (message : M) (groups : List G) (rows : List (List F))
    (messageValid : layout.hash.scheme.message.valid message) (groupLength : groups.length ≤ layout.groups)
    (rowLength : rows.length ≤ layout.rows) (coefficientLengths : ∀ row ∈ rows, row.length ≤ layout.hash.coefficients) :
    layout.input.valid (message, groups, rows, encodeState state) :=
  input_valid layout scalars points state message groups rows messageValid groupLength rowLength coefficientLengths
    (room.encoded layout.hash.scheme scalars points) (by have := room.2.1; omega)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.HashDispatch
