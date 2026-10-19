import Signatures.Runtime.Caliper.Finite
import Signatures.Runtime.Caliper.NameBounds
import Signatures.Runtime.Caliper.DataBudgets

/-! Test a represented finite counter for zero using an actual word comparison.
The range may occupy the entire word domain; no conversion or modulus is used. -/
namespace Signatures.Runtime.CaliperBackend.BoundedSource.Finite
open Caliper
variable {w : Nat} (bound : Nat) (hw : 16 < 2 ^ w) (fits : bound + 1 ≤ 2 ^ w)

include hw fits in
theorem word_zero (value : Fin (bound + 1)) :
    BitVec.ofNat w value.val = 0 ↔ value = 0 := by
  change BitVec.ofNat w value.val = BitVec.ofNat w 0 ↔ value = 0
  rw [Natural.words_equal value.val 0 (value.isLt.trans_le fits) (by omega)]
  exact ⟨fun equal => Fin.ext equal, fun equal => congrArg Fin.val equal⟩

def isZero : Implementation .unit (layout bound hw fits)
    (DataImplementation.boolLayout w (width_pos hw)) (fun value => decide (value = 0)) where
  preserves _ _ := trivial
  program := {
    code := CellArithmetic.code 0 .eq 0
    positive_width := width_pos hw
    description_fits := CellArithmetic.descriptionFits _ _ _ hw
    random_free := CellArithmetic.randomFree _ _ _
    time _ := 5
    net _ := 0
    workspace _ := 0
    correct := by
      intro tape value before represented
      have contents : (before.bufs 0).toList = [BitVec.ofNat w value.val.val] := represented.2.1
      obtain ⟨after, execution, result, zero, caps⟩ := CellArithmetic.exec_at .unit tape [] []
        (BitVec.ofNat w value.val.val) 0 .eq before contents (by simp)
      refine ⟨after, 0, 0, execution, ⟨zero.trans represented.1, ?_,
        execution.wellFormed_preserved represented.2.2.1, ?_⟩, le_rfl, le_rfl⟩
      · change (after.bufs 0).toList = [if decide (value.val = 0) then 1 else 0]
        simpa only [List.nil_append, BinOp.eval, word_zero bound hw fits, decide_eq_true_eq] using result
      · intro buffer; rw [caps]; exact represented.2.2.2 buffer }

theorem isZero_bounded : (isZero bound hw fits).BoundedBy 5 23 := ⟨fun _ => le_rfl, le_rfl⟩
theorem isZero_buffers : (isZero bound hw fits).program.code.memBound ≤ 1 := by rfl
theorem isZero_names (slots : Nat) : NamesAccounted (isZero bound hw fits).program.code slots :=
  CellArithmetic.names _ _ _ _

end Signatures.Runtime.CaliperBackend.BoundedSource.Finite
