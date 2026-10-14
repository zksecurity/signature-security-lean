import Signatures.Runtime.BackendIndexCost
import Signatures.Runtime.BackendReverseCost
import Signatures.Runtime.BackendLazyAGMOutputSize
import Signatures.Runtime.BackendTokenRows
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor Signatures.Runtime Signatures.Runtime.BackendProgram

namespace SignaturesTest.BackendExtractionLists

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

section Execution

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase (ZMod 5) (ZMod 5) (ZMod 5) Nat Nat))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b)
      ((arithmetic (ZMod 5) (ZMod 5) (ZMod 5) Nat Nat cost).execute instr))

private def contextualIndex : Expr CryptoOp
    [.nat, scalar, .list scalar, .list scalar, .nat] scalar :=
  (index .natEq .natSub).weakenTail [.list scalar, .nat]

-- Native compilation retains a nonempty environment. Its saved list must not
-- replace the queried coefficients; a suffix after the hit changes no answer.
example : (Code.atomic (Q := Q) (iface := iface)
    (Expression.compile rep data _ primitive contextualIndex)).denote
      (1, 0, [2, 3, 4, 1], [4, 0], 99, ()) = pure (3 : ZMod 5) := by
  rfl

-- Zero is a valid coefficient, and an out-of-range index defaults to zero even
-- when the retained context contains an entry at that position.
example : (Code.atomic (Q := Q) (iface := iface)
    (Expression.compile rep data _ primitive contextualIndex)).denote
      (0, 0, [0, 4], [3], 99, ()) = pure (0 : ZMod 5) := by
  rfl

example : (Code.atomic (Q := Q) (iface := iface)
    (Expression.compile rep data _ primitive contextualIndex)).denote
      (2, 0, [2], [1, 3, 4], 99, ()) = pure (0 : ZMod 5) := by
  rfl

-- Reversal restores chronological occurrences without deduplicating replies
-- and works with a retained coefficient list and counter.
example : (Code.atomic (Q := Q) (iface := iface)
    (Expression.compile rep data _ primitive
      (reverseList (cell := AGM.tokenTy message) (Γ := [.list scalar, .nat])))).denote
      ([(7, 2), (8, 4), (7, 1)], [1, 3], 99, ()) =
        pure ([(7, 1), (8, 4), (7, 2)] : List (Nat × ZMod 5)) := by
  rfl

-- Coefficients follow chronological occurrences, including repeats. Missing
-- entries become zero; excess entries do not create additional rows.
example : (Code.atomic (Q := Q) (iface := iface)
    (Expression.compile rep data _ primitive (AGM.tokenRows (dataTy := message)))).denote
      ([(7, 2), (8, 4), (7, 1)], [3, 4], ()) =
        pure ([((7, 1), 3), ((8, 4), 4), ((7, 2), 0)] : List ((Nat × ZMod 5) × ZMod 5)) := by
  rfl

example : (Code.atomic (Q := Q) (iface := iface)
    (Expression.compile rep data _ primitive (AGM.tokenRows (dataTy := message)))).denote
      ([(7, 2)], [3, 4, 1], ()) =
        pure ([((7, 2), 3)] : List ((Nat × ZMod 5) × ZMod 5)) := by
  rfl

-- The full attachment component also supports a nonzero default. Repeated
-- keys remain distinct occurrences, and the extra context supplies no cells.
example : (Code.atomic (Q := Q) (iface := iface)
    (Expression.compile rep data _ primitive
      ((AGM.attachTable (indexTy := message)).weakenTail [.list scalar, .nat]))).denote
      (4, [7, 8, 7], [0, 3], [2, 2, 2], 99, ()) =
        pure ([(7, 0), (8, 3), (7, 4)] : List (Nat × ZMod 5)) := by
  rfl

example : (Code.atomic (Q := Q) (iface := iface)
    (Expression.compile rep data _ primitive
      ((AGM.tokenRows (dataTy := message)).weakenTail [.list scalar, .nat]))).denote
      ([(7, 2), (8, 4), (7, 1)], [3, 4], [1, 1, 1], 99, ()) =
        pure ([((7, 1), 3), ((8, 4), 4), ((7, 2), 0)] : List ((Nat × ZMod 5) × ZMod 5)) := by
  rfl

-- Empty transcripts do not turn surplus coefficients into rows.
example : (Code.atomic (Q := Q) (iface := iface)
    (Expression.compile rep data _ primitive
      ((AGM.tokenRows (dataTy := message)).weakenTail [.list scalar, .nat]))).denote
      ([], [3, 4, 1], [1, 1, 1], 99, ()) =
        pure ([] : List ((Nat × ZMod 5) × ZMod 5)) := by
  rfl

end Execution

-- A zero-size encoding cannot satisfy the length-recovery contract. This
-- prevents treating an upper encoding bound alone as a coefficient-count cap.
example {C : StepClass} {Q : QuantitativeStepClass C} (data : DataRepresentation C)
    (laws : ListLengthLaws Q data)
    (zero : Q.size (data.list data.unit) [()] = 0) : False := by
  have h := laws.length_le_size data.unit [()]
  simp only [List.length_cons, List.length_nil, zero] at h
  omega

open Lean Meta Elab Command

run_cmd liftTermElabM do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``foldWork_bound_remaining,
      ``IndexCompiler.body_time_bound, ``IndexCompiler.index_time_bound_of_caps,
      ``IndexCompiler.index_cost_bound, ``IndexCompiler.index_description,
      ``ReverseCompiler.body_time_bound, ``ReverseCompiler.reverse_time_bound,
      ``ReverseCompiler.reverse_cost_bound, ``ReverseCompiler.reverse_description,
      ``AttachCompiler.remaining_step, ``AttachCompiler.remaining_fold,
      ``AttachCompiler.rows_encoded_size, ``AttachCompiler.state_encoded_size, ``AttachCompiler.body_frame_size,
      ``AttachCompiler.body_time_bound, ``AttachCompiler.body_denote, ``AttachCompiler.fold_time_bound,
      ``AttachCompiler.fold_denote, ``AttachCompiler.table_denote,
      ``AttachCompiler.table_time_bound, ``AttachCompiler.table_cost_bound, ``AttachCompiler.table_description,
      ``TokenCompiler.rows_denote, ``TokenCompiler.rows_time_bound, ``TokenCompiler.rows_output_size,
      ``TokenCompiler.rows_cost_bound, ``TokenCompiler.rows_description,
      ``ListLengthLaws.length_le_size, ``ListLengthLaws.of_additive,
      ``LazyAGM.coefficient_lengths_le_output, ``LazyAGM.coefficient_lengths_of_output_cap] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: finite-domain premise added to extraction list accounting"

end SignaturesTest.BackendExtractionLists
