import Proofs.Runtime.Caliper.ConstructedArithmetic

/-! Literal addition on a represented natural. The operation updates the stored
word directly and proves the result cannot wrap on the admitted input domain. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.Constructed
open Caliper
variable {w : Nat}

def addLiteral (bound amount : Nat) (hw : 16 < 2 ^ w) (fits : bound + amount ≤ 2 ^ w) :
    Constructed (Layout.counter w bound (width_pos hw) (by omega))
      (Layout.counter w (bound + amount) (width_pos hw) fits) (fun value => value + amount) where
  implementation :=
    { preserves := fun value valid => Nat.add_lt_add_right valid amount
      program :=
        { code := CellArithmetic.code 0 .add (BitVec.ofNat w amount)
          positive_width := width_pos hw
          description_fits := CellArithmetic.descriptionFits _ _ _ hw
          random_free := CellArithmetic.randomFree _ _ _
          time _ := 5
          net _ := 0
          workspace _ := 0
          correct := by
            intro tape value before represented
            have contents : (before.bufs 0).toList = [BitVec.ofNat w value.val] := represented.2.1
            obtain ⟨after, execution, result, zero, caps⟩ := CellArithmetic.exec_at .unit tape [] []
              (BitVec.ofNat w value.val) (BitVec.ofNat w amount) .add before contents (by simp)
            refine ⟨after, 0, 0, execution, ⟨zero.trans represented.1, ?_,
              execution.wellFormed_preserved represented.2.2.1, ?_⟩, le_rfl, le_rfl⟩
            · change (after.bufs 0).toList = [BitVec.ofNat w (value.val + amount)]
              simpa only [List.nil_append, BinOp.eval, BitVec.ofNat_add] using result
            · intro buffer
              rw [caps]
              exact represented.2.2.2 buffer } }
  budget := ⟨5, 23⟩
  bounded := ⟨fun _ => le_rfl, (CellArithmetic.descriptionWords_eq _ _ _).le⟩
  buffers := 1
  buffers_le := CellArithmetic.buffers _ _ _
  names := CellArithmetic.names _ _ _

end Signatures.Runtime.CaliperBackend.BoundedSource.Constructed
