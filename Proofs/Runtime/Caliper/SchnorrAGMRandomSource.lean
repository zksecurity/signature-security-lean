import Proofs.Runtime.Caliper.SchnorrAGMRandom

/-! The constructed handler has the original joint reply/state law, including
the uniform draw made on malformed requests. Representability needs no free slots. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
open Caliper BoundedSource OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G : Type} (layout : Layouts w M F G qH qS randomBound)

theorem source_original [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]
    (g pk : G) (state : Signatures.Runtime.SchnorrAGM.State F G M) (n : Nat) (groups : List G) (rows : List (List F))
    (valid : layout.input.valid (groups, rows, n, encodeState state)) :
    Subtype.val <$> source layout ⟨(groups, rows, n, encodeState state), valid⟩ =
      (fun result => ((result.1.data.val, result.1.groups ()), encodeState result.2)) <$>
        (Signatures.Runtime.SchnorrAGM.handler g pk ⟨⟨.random n, fun _ => groups⟩, fun _ => rows⟩).run state := by
  rw [erase]
  cases groups <;> simp only [Signatures.Runtime.SchnorrAGM.handler, StateT.run, List.cons_ne_nil, ite_true, ite_false,
    bind_pure_comp, Functor.map_map, List.isEmpty_nil, List.isEmpty_cons] <;> rfl

theorem input_valid [Field F] (scalars : ∀ value, layout.scheme.scalar.valid value) (points : ∀ value, layout.scheme.point.valid value)
    (state : Signatures.Runtime.SchnorrAGM.State F G M) (n : Nat) (groups : List G) (rows : List (List F))
    (range : n ≤ randomBound) (groupLength : groups.length ≤ layout.groups)
    (rowLength : rows.length ≤ layout.rows) (coefficientLengths : ∀ row ∈ rows, row.length ≤ layout.coefficients)
    (stateValid : layout.scheme.state.valid (encodeState state)) :
    layout.input.valid (groups, rows, n, encodeState state) :=
  ⟨⟨groupLength, fun point _ => points point⟩,
    ⟨rowLength, fun row member => ⟨coefficientLengths row member, fun scalar _ => scalars scalar⟩⟩,
    by change n < randomBound + 1; omega, stateValid⟩

theorem reserved_input [Field F] (scalars : ∀ value, layout.scheme.scalar.valid value) (points : ∀ value, layout.scheme.point.valid value)
    {hashes signatures : Nat} {state : Signatures.Runtime.SchnorrAGM.State F G M}
    (room : layout.scheme.Reserved hashes signatures state) (n : Nat) (groups : List G) (rows : List (List F))
    (range : n ≤ randomBound) (groupLength : groups.length ≤ layout.groups)
    (rowLength : rows.length ≤ layout.rows) (coefficientLengths : ∀ row ∈ rows, row.length ≤ layout.coefficients) :
    layout.input.valid (groups, rows, n, encodeState state) :=
  input_valid layout scalars points state n groups rows range groupLength rowLength coefficientLengths
    (CaliperBackend.SchnorrAGM.Layouts.Reserved.encoded layout.scheme room scalars points)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
