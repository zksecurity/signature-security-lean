import Signatures.Runtime.Caliper.SchnorrAGMHandlerHash

/-! Common-store hashing preserves the original handler's joint reply/state
law and the represented runtime generator/public key. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.HashComponent
open Caliper BoundedSource OracleComp OracleSpec Schnorr.AGM AlgebraicGroupModel.Interaction
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G : Type} [Field F]
    [DecidableEq F] [DecidableEq M] [DecidableEq G]
    (layout : Handler.Layouts w M F G qH qS randomBound) (zeroValid : layout.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

theorem source_original [AddCommGroup G] [Module F G] [SampleableType F]
    (sampler : ProbComp layout.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampler = ($ᵗ F : ProbComp F))
    (g pk : G) (state : Signatures.Runtime.SchnorrAGM.State F G M) (message : M) (groups : List G) (rows : List (List F))
    (valid : layout.hashInput.valid ((message, groups, rows), (g, pk), encodeState state)) :
    Subtype.val <$> source layout zeroValid mul add mulBuffers addBuffers reserve sampler
      ⟨((message, groups, rows), (g, pk), encodeState state), valid⟩ =
      (fun result => ((result.1.data, result.1.groups ()), (g, pk), encodeState result.2)) <$>
        (Signatures.Runtime.SchnorrAGM.handler g pk ⟨⟨.hash message, fun _ => groups⟩, fun _ => rows⟩).run state := by
  rw [erase]
  have core := HashDispatch.source_original layout.hash zeroValid mul add mulBuffers addBuffers reserve sampler uniform
    g pk state message groups rows (layout.hashValue ⟨((message, groups, rows), (g, pk), encodeState state), valid⟩).property
  have lifted := congrArg (Functor.map (fun p : Message F (Group G) × EncodedState F G M =>
    ((p.1.data, p.1.groups ()), (g, pk), p.2))) core
  dsimp only [OracleSpec.Range, explainedSpec, Reply] at lifted ⊢
  simp only [Functor.map_map] at lifted
  exact lifted

omit [DecidableEq F] in
theorem input_valid (scalars : ∀ value, layout.scheme.scalar.valid value) (points : ∀ value, layout.scheme.point.valid value)
    (g pk : G) (state : Signatures.Runtime.SchnorrAGM.State F G M) (message : M) (groups : List G) (rows : List (List F))
    (messageValid : layout.scheme.message.valid message) (groupLength : groups.length ≤ layout.groups)
    (rowLength : rows.length ≤ layout.rows) (coefficientLengths : ∀ row ∈ rows, row.length ≤ layout.coefficients)
    (stateValid : layout.scheme.state.valid (encodeState state)) (spare : state.cache.length ≤ qH + qS) :
    layout.hashInput.valid ((message, groups, rows), (g, pk), encodeState state) := by
  have core := HashDispatch.input_valid layout.hash scalars points state message groups rows messageValid groupLength
    rowLength coefficientLengths stateValid spare
  exact ⟨⟨⟨core.1.1, core.1.2.1, core.1.2.2.1⟩, ⟨points g, points pk⟩, core.1.2.2.2⟩, core.2⟩

omit [DecidableEq F] in
theorem reserved_input (scalars : ∀ value, layout.scheme.scalar.valid value) (points : ∀ value, layout.scheme.point.valid value)
    {hashes signatures : Nat} {state : Signatures.Runtime.SchnorrAGM.State F G M}
    (room : layout.scheme.Reserved hashes signatures state) (g pk : G) (message : M) (groups : List G) (rows : List (List F))
    (messageValid : layout.scheme.message.valid message) (groupLength : groups.length ≤ layout.groups)
    (rowLength : rows.length ≤ layout.rows) (coefficientLengths : ∀ row ∈ rows, row.length ≤ layout.coefficients) :
    layout.hashInput.valid ((message, groups, rows), (g, pk), encodeState state) :=
  input_valid layout scalars points g pk state message groups rows messageValid groupLength rowLength coefficientLengths
    (room.encoded layout.scheme scalars points) (by have := room.2.1; omega)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.HashComponent
