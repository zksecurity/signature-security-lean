import Proofs.Runtime.Caliper.SchnorrAGMHandlerSigning

/-! Common-store signing has the original joint reply/state law and preserves
the runtime configuration. Malformed inputs keep the core's conditional guard. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.SigningComponent
open Caliper BoundedSource OracleComp OracleSpec Schnorr.AGM AlgebraicGroupModel.Interaction
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq M] [DecidableEq G]
    (layout : Handler.Layouts w M F G qH qS randomBound) (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.arithmetic.arithmetic.scaleArgs layout.scheme.point (fun args => args.1 • args.2))
    (sub : Implementation .unit layout.arithmetic.arithmetic.points layout.scheme.point (fun args => args.1 - args.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

theorem source_original [DecidableEq F] [SampleableType F]
    (sampler : ProbComp layout.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampler = ($ᵗ F : ProbComp F))
    (g pk : G) (state : Signatures.Runtime.SchnorrAGM.State F G M) (message : M) (groups : List G) (rows : List (List F))
    (valid : layout.signingInput.valid ((message, groups, rows), (g, pk), encodeState state)) :
    Subtype.val <$> source layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler
      ⟨((message, groups, rows), (g, pk), encodeState state), valid⟩ =
      (fun result => ((result.1.data, result.1.groups ()), (g, pk), encodeState result.2)) <$>
        (Signatures.Runtime.SchnorrAGM.handler g pk ⟨⟨.sign message, fun _ => groups⟩, fun _ => rows⟩).run state := by
  rw [erase]
  have core := SigningDispatch.source_original layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler uniform
    g pk state message groups rows (layout.signingValue ⟨((message, groups, rows), (g, pk), encodeState state), valid⟩).property
  have lifted := congrArg (Functor.map (fun p : Message F (Group G) × EncodedState F G M =>
    ((p.1.data, p.1.groups ()), (g, pk), p.2))) core
  dsimp only [OracleSpec.Range, explainedSpec, Reply] at lifted ⊢
  simp only [Functor.map_map] at lifted
  exact lifted

omit [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G] in
theorem input_valid (scalars : ∀ value, layout.scheme.scalar.valid value) (points : ∀ value, layout.scheme.point.valid value)
    (g pk : G) (state : Signatures.Runtime.SchnorrAGM.State F G M) (message : M) (groups : List G) (rows : List (List F))
    (messageValid : layout.scheme.message.valid message) (groupLength : groups.length ≤ layout.groups)
    (rowLength : rows.length ≤ layout.rows) (coefficientLengths : ∀ row ∈ rows, row.length ≤ layout.coefficients)
    (stateValid : layout.scheme.state.valid (encodeState state))
    (spare : groups = [] → Signing.Sampling.ready layout.histories (g, pk, message, encodeState state)) :
    layout.signingInput.valid ((message, groups, rows), (g, pk), encodeState state) := by
  have core := SigningDispatch.input_valid layout.signing scalars points state g pk message groups rows messageValid groupLength
    rowLength coefficientLengths stateValid spare
  exact ⟨⟨⟨messageValid, core.1.1, core.1.2.1⟩, ⟨points g, points pk⟩, stateValid⟩, core.2⟩

omit [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G] in
theorem reserved_input (scalars : ∀ value, layout.scheme.scalar.valid value) (points : ∀ value, layout.scheme.point.valid value)
    {hashes signatures : Nat} {state : Signatures.Runtime.SchnorrAGM.State F G M}
    (room : layout.scheme.Reserved hashes (signatures + 1) state) (g pk : G) (message : M) (groups : List G) (rows : List (List F))
    (messageValid : layout.scheme.message.valid message) (groupLength : groups.length ≤ layout.groups)
    (rowLength : rows.length ≤ layout.rows) (coefficientLengths : ∀ row ∈ rows, row.length ≤ layout.coefficients) :
    layout.signingInput.valid ((message, groups, rows), (g, pk), encodeState state) :=
  input_valid layout scalars points g pk state message groups rows messageValid groupLength rowLength coefficientLengths
    (CaliperBackend.SchnorrAGM.Layouts.Reserved.encoded layout.scheme room scalars points)
    (fun _ => Signing.Sampling.reserved_ready layout.histories room g pk message)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.SigningComponent
