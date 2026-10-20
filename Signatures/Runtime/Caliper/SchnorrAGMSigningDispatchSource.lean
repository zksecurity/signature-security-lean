import Signatures.Runtime.Caliper.SchnorrAGMSigningDispatch

/-! Exact original-handler correspondence for all signing request shapes.
Only accepted requests require space for a signature; coefficient rows are
represented input data and ignored by the original handler on both paths. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.SigningDispatch
open Caliper BoundedSource OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS : Nat} {M F G : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq M] [DecidableEq G] (layout : Layouts w M F G qH qS)
    (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.signing.signing.arithmetic.scaleArgs layout.scheme.point (fun args => args.1 • args.2))
    (sub : Implementation .unit layout.signing.signing.arithmetic.points layout.scheme.point (fun args => args.1 - args.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

theorem source_original [DecidableEq F] [SampleableType F]
    (sampler : ProbComp layout.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampler = ($ᵗ F : ProbComp F))
    (g pk : G) (state : Signatures.Runtime.SchnorrAGM.State F G M) (message : M) (groups : List G) (rows : List (List F))
    (valid : layout.input.valid (groups, rows, g, pk, message, encodeState state)) :
    (fun value => (decodeGroupReply value.val.1, value.val.2)) <$>
      source layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler
        ⟨(groups, rows, g, pk, message, encodeState state), valid⟩ =
      (fun result => (result.1, encodeState result.2)) <$>
        (Signatures.Runtime.SchnorrAGM.handler g pk ⟨⟨.sign message, fun _ => groups⟩, fun _ => rows⟩).run state := by
  cases groups with
  | nil =>
      rw [source_yes layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler _ rfl]
      simp only [Functor.map_map]
      exact Signing.Sampling.source_original layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve
        sampler uniform state g pk message rows (layout.acceptedValue ⟨([], rows, g, pk, message, encodeState state), valid, rfl⟩).property
  | cons point rest =>
      rw [source_no layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler _ rfl]
      simp only [map_pure, Signatures.Runtime.SchnorrAGM.handler, StateT.run, List.cons_ne_nil,
        ne_eq, not_false_eq_true, ite_true]
      rfl

omit [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G] in
theorem input_valid (scalars : ∀ value, layout.scheme.scalar.valid value) (points : ∀ value, layout.scheme.point.valid value)
    (state : Signatures.Runtime.SchnorrAGM.State F G M) (g pk : G) (message : M) (groups : List G) (rows : List (List F))
    (messageValid : layout.scheme.message.valid message) (groupLength : groups.length ≤ layout.groups)
    (rowLength : rows.length ≤ layout.rows) (coefficientLengths : ∀ row ∈ rows, row.length ≤ layout.coefficients)
    (stateValid : layout.scheme.state.valid (encodeState state))
    (spare : groups = [] → Signing.Sampling.ready layout.signing (g, pk, message, encodeState state)) :
    layout.input.valid (groups, rows, g, pk, message, encodeState state) := by
  refine ⟨⟨⟨groupLength, fun point _ => points point⟩,
    ⟨rowLength, fun row member => ⟨coefficientLengths row member, fun scalar _ => scalars scalar⟩⟩,
    points g, points pk, messageValid, stateValid⟩, ?_⟩
  intro empty
  apply spare
  cases groups with
  | nil => rfl
  | cons point rest => contradiction

omit [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G] in
theorem reserved_input (scalars : ∀ value, layout.scheme.scalar.valid value) (points : ∀ value, layout.scheme.point.valid value)
    {hashes signatures : Nat} {state : Signatures.Runtime.SchnorrAGM.State F G M}
    (room : layout.scheme.Reserved hashes (signatures + 1) state) (g pk : G) (message : M) (groups : List G) (rows : List (List F))
    (messageValid : layout.scheme.message.valid message) (groupLength : groups.length ≤ layout.groups)
    (rowLength : rows.length ≤ layout.rows) (coefficientLengths : ∀ row ∈ rows, row.length ≤ layout.coefficients) :
    layout.input.valid (groups, rows, g, pk, message, encodeState state) :=
  input_valid layout scalars points state g pk message groups rows messageValid groupLength rowLength coefficientLengths
    (CaliperBackend.SchnorrAGM.Layouts.Reserved.encoded layout.scheme room scalars points)
    (fun _ => Signing.Sampling.reserved_ready layout.signing room g pk message)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.SigningDispatch
