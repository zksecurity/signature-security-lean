import Proofs.Runtime.Caliper.TokenEvaluationPrepare

/-! Transcript preparation counts coefficient storage, zero construction and
all copies of the cache as well as the actual chronological row program. -/
namespace Signatures.Runtime.CaliperBackend.TokenEvaluation
open Caliper BoundedSource
variable {w : Nat} {K G F R : Type} (layout : Layouts w K G F R)
    (coefficientDefault : layout.rows.accumulation.coefficient.Value)
    (initial : layout.rows.accumulation.cache.value.Value)

theorem rows_bounded : (rows layout coefficientDefault).BoundedBy
    (16 * layout.width + TokenRows.timeBudget layout.assembly)
    (52 * layout.width + 15 + TokenRows.codeBudget layout.assembly) := by
  apply ((Implementation.first_boundedBy (TokenRows.input layout.assembly) layout.rows.accumulation.cache.lookup.table
    layout.rows.accumulation.cache.wordFits _).then (TokenRows.bounded layout.assembly coefficientDefault)).mono
  all_goals have := TokenRows.input_size layout.assembly; have := layout.base_sizes; omega
theorem cache_bounded : (cache layout).BoundedBy (8 * layout.width) (26 * layout.width + 14) := by
  apply (Implementation.second_boundedBy _ _ _ _).mono
  all_goals have := layout.base_sizes; omega
theorem accumulator_bounded : (accumulator layout initial).BoundedBy (8 * layout.width) (26 * layout.width + 14) := by
  apply (Implementation.constant_bounded _ _ _ _).mono
  all_goals have := layout.base_sizes; omega
theorem state_bounded : (state layout initial).BoundedBy (224 * layout.width) (728 * layout.width + 152) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (accumulator_bounded layout initial) (cache_bounded layout)).mono
  all_goals have := layout.input_size; have := layout.base_sizes; omega
def prepareTime : Nat := 448 * layout.width + TokenRows.timeBudget layout.assembly
def prepareWords : Nat := 1456 * layout.width + 291 + TokenRows.codeBudget layout.assembly
theorem prepare_bounded : (prepare layout coefficientDefault initial).BoundedBy (prepareTime layout) (prepareWords layout) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (rows_bounded layout coefficientDefault) (state_bounded layout initial)).mono
  all_goals dsimp only [prepareTime, prepareWords]; have := layout.input_size; have := layout.base_sizes; omega

theorem rows_names (names : Nat) : NamesAccounted (rows layout coefficientDefault).program.code names :=
  (Implementation.first_names _ _ _ _ names).seq (TokenRows.names layout.assembly coefficientDefault names)
theorem cache_names (names : Nat) : NamesAccounted (cache layout).program.code names := Implementation.second_names _ _ _ _ names
theorem accumulator_names (names : Nat) : NamesAccounted (accumulator layout initial).program.code names := Implementation.constant_names _ _ _ _ names
theorem state_names (names : Nat) : NamesAccounted (state layout initial).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (accumulator_names layout initial names) (cache_names layout names)
theorem prepare_names (names : Nat) : NamesAccounted (prepare layout coefficientDefault initial).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (rows_names layout coefficientDefault names) (state_names layout initial names)
end Signatures.Runtime.CaliperBackend.TokenEvaluation
