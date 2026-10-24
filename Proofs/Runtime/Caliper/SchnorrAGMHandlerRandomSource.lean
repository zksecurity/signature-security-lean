import Proofs.Runtime.Caliper.SchnorrAGMHandlerRandom

/-! Common-store randomness has the original handler's joint reply/state law;
the runtime generator and public key are preserved exactly. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.RandomComponent
open Caliper BoundedSource OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G : Type}
  (layout : Handler.Layouts w M F G qH qS randomBound)

theorem source_original [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]
    (g pk : G) (state : Signatures.Runtime.SchnorrAGM.State F G M) (n : Nat) (groups : List G) (rows : List (List F))
    (valid : layout.randomInput.valid ((n, groups, rows), (g, pk), encodeState state)) :
    Subtype.val <$> source layout ⟨((n, groups, rows), (g, pk), encodeState state), valid⟩ =
      (fun result => ((result.1.data.val, result.1.groups ()), (g, pk), encodeState result.2)) <$>
        (Signatures.Runtime.SchnorrAGM.handler g pk ⟨⟨.random n, fun _ => groups⟩, fun _ => rows⟩).run state := by
  rw [erase]
  cases groups <;> simp only [Signatures.Runtime.SchnorrAGM.handler, StateT.run, List.cons_ne_nil, ite_true, ite_false,
    bind_pure_comp, Functor.map_map, List.isEmpty_nil, List.isEmpty_cons] <;> rfl

theorem input_valid [Field F] (scalars : ∀ value, layout.scheme.scalar.valid value)
    (points : ∀ value, layout.scheme.point.valid value)
    (g pk : G) (state : Signatures.Runtime.SchnorrAGM.State F G M) (n : Nat) (groups : List G) (rows : List (List F))
    (range : n ≤ randomBound) (groupLength : groups.length ≤ layout.groups)
    (rowLength : rows.length ≤ layout.rows) (coefficientLengths : ∀ row ∈ rows, row.length ≤ layout.coefficients)
    (stateValid : layout.scheme.state.valid (encodeState state)) :
    layout.randomInput.valid ((n, groups, rows), (g, pk), encodeState state) := by
  have core := SchnorrAGM.Random.input_valid layout.random scalars points state n groups rows range groupLength
    rowLength coefficientLengths stateValid
  exact ⟨⟨core.2.2.1, core.1, core.2.1⟩, ⟨points g, points pk⟩, core.2.2.2⟩

theorem reserved_input [Field F] (scalars : ∀ value, layout.scheme.scalar.valid value)
    (points : ∀ value, layout.scheme.point.valid value)
    {hashes signatures : Nat} {state : Signatures.Runtime.SchnorrAGM.State F G M}
    (room : layout.scheme.Reserved hashes signatures state) (g pk : G) (n : Nat) (groups : List G) (rows : List (List F))
    (range : n ≤ randomBound) (groupLength : groups.length ≤ layout.groups)
    (rowLength : rows.length ≤ layout.rows) (coefficientLengths : ∀ row ∈ rows, row.length ≤ layout.coefficients) :
    layout.randomInput.valid ((n, groups, rows), (g, pk), encodeState state) :=
  input_valid layout scalars points g pk state n groups rows range groupLength rowLength coefficientLengths
    (CaliperBackend.SchnorrAGM.Layouts.Reserved.encoded layout.scheme room scalars points)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.RandomComponent
