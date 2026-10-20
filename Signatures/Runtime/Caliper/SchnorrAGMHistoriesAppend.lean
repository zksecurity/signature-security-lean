import Signatures.Runtime.Caliper.SchnorrAGMHistoriesPair

/-! Each history receives its corresponding runtime entry. The original input
invariant supplies both free slots; no whole append implementation is assumed. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Histories
open Caliper BoundedSource
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def basisPair : Implementation .unit layout.input layout.basisAppend.raw
    (fun input => (input.2.2.1, input.2.2.2.2.1)) :=
  combine layout (selectAffine layout) (selectBasis layout)
    (by have := selection_buffers layout; omega) (by have := selection_buffers layout; omega)
    (by have := layout.field_sizes; omega) (by have := layout.field_sizes; omega)
def signedPair : Implementation .unit layout.input layout.signedAppend.raw
    (fun input => (input.2.2.2.1, input.2.2.2.2.2.1)) :=
  combine layout (selectMessage layout) (selectSigned layout)
    (by have := selection_buffers layout; omega) (by have := selection_buffers layout; omega)
    (by have := layout.field_sizes; omega) (by have := layout.field_sizes; omega)
def basisArguments : Implementation .unit layout.input layout.basisAppend.input
    (fun input => (input.2.2.1, input.2.2.2.2.1)) :=
  (basisPair layout).restrictOutput (fun input => input.2.length < qS + 2) (fun _ valid => valid.2.1)
def signedArguments : Implementation .unit layout.input layout.signedAppend.input
    (fun input => (input.2.2.2.1, input.2.2.2.2.2.1)) :=
  (signedPair layout).restrictOutput (fun input => input.2.length < qS) (fun _ valid => valid.2.2)
def appendBasis : Implementation .unit layout.input layout.scheme.basis
    (fun input => input.2.2.2.2.1 ++ [input.2.2.1]) :=
  (basisArguments layout).then (ListSnoc.implementation layout.basisAppend)
def appendSigned : Implementation .unit layout.input layout.scheme.signed
    (fun input => input.2.2.2.2.2.1 ++ [input.2.2.2.1]) :=
  (signedArguments layout).then (ListSnoc.implementation layout.signedAppend)

theorem basisPair_buffers : (basisPair layout).program.code.memBound ≤ 3 :=
  combine_buffers layout _ _ _ _ _ _ (selection_buffers layout).2.2.1 (selection_buffers layout).2.2.2.2.1
theorem signedPair_buffers : (signedPair layout).program.code.memBound ≤ 3 :=
  combine_buffers layout _ _ _ _ _ _ (selection_buffers layout).2.2.2.1 (selection_buffers layout).2.2.2.2.2.1
theorem appendBasis_buffers : (appendBasis layout).program.code.memBound ≤ 4 :=
  max_le ((basisPair_buffers layout).trans (by decide)) (ListSnoc.buffers layout.basisAppend)
theorem appendSigned_buffers : (appendSigned layout).program.code.memBound ≤ 4 :=
  max_le ((signedPair_buffers layout).trans (by decide)) (ListSnoc.buffers layout.signedAppend)

theorem appendBasis_names (slots : Nat) : NamesAccounted (appendBasis layout).program.code slots := by
  have paired : NamesAccounted (basisPair layout).program.code slots :=
    combine_names layout _ _ _ _ _ _ slots (selection_names layout slots).2.2.1 (selection_names layout slots).2.2.2.2.1
  exact paired.seq (ListSnoc.names layout.basisAppend slots)
theorem appendSigned_names (slots : Nat) : NamesAccounted (appendSigned layout).program.code slots := by
  have paired : NamesAccounted (signedPair layout).program.code slots :=
    combine_names layout _ _ _ _ _ _ slots (selection_names layout slots).2.2.2.1 (selection_names layout slots).2.2.2.2.2.1
  exact paired.seq (ListSnoc.names layout.signedAppend slots)

theorem basisPair_bounded : (basisPair layout).BoundedBy (600 * layout.width) (1950 * layout.width + 304) := by
  apply (combine_bounded layout _ _ _ _ _ _ (selection_bounded layout).2.2.1 (selection_bounded layout).2.2.2.2.1).mono <;> omega
theorem signedPair_bounded : (signedPair layout).BoundedBy (600 * layout.width) (1950 * layout.width + 304) := by
  apply (combine_bounded layout _ _ _ _ _ _ (selection_bounded layout).2.2.2.1 (selection_bounded layout).2.2.2.2.2.1).mono <;> omega
theorem appendBasis_bounded : (appendBasis layout).BoundedBy
    (ListSnoc.timeBudget layout.basisAppend + 600 * layout.width)
    (ListSnoc.codeBudget layout.basisAppend + 1950 * layout.width + 305) := by
  apply (((basisPair_bounded layout).restrictOutput (fun input => input.2.length < qS + 2) (fun _ valid => valid.2.1)).then
    (ListSnoc.bounded layout.basisAppend)).mono <;> omega
theorem appendSigned_bounded : (appendSigned layout).BoundedBy
    (ListSnoc.timeBudget layout.signedAppend + 600 * layout.width)
    (ListSnoc.codeBudget layout.signedAppend + 1950 * layout.width + 305) := by
  apply (((signedPair_bounded layout).restrictOutput (fun input => input.2.length < qS) (fun _ valid => valid.2.2)).then
    (ListSnoc.bounded layout.signedAppend)).mono <;> omega

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Histories
