import Proofs.Runtime.Caliper.SumContextMerge

/-! Reconstruction uses a fixed scratch-buffer extent independent of payload
and saved-context widths. Copying the complete context remains charged. -/
namespace Signatures.Runtime.CaliperBackend.SumContext
open Caliper
variable {w : Nat} {A B S : Type}
    (left : Representation w A) (right : Representation w B) (saved : Representation w S)
    (hw : 16 < 2 ^ w) (fits : 1 + max left.encoding.words right.encoding.words + saved.encoding.words < 2 ^ w)

theorem mergeLeft_buffers : (mergeLeft left right saved hw fits).code.memBound ≤ 4 := by
  let tagged := inlRealizer .unit (by decide) left right hw (by omega)
  have bounded := (inl_names left right hw (by omega)).buffers
  change tagged.code.memBound ≤ 3 at bounded
  have retained := (Retain.code_names tagged.code (max 2 tagged.code.memBound)
    left.encoding.words (1 + max left.encoding.words right.encoding.words) saved.encoding.words
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)).2
  change (mergeLeft left right saved hw fits).code.memBound ≤ _ at retained
  exact retained.trans (by change max 2 tagged.code.memBound + 1 ≤ 4; omega)

theorem mergeRight_buffers : (mergeRight left right saved hw fits).code.memBound ≤ 4 := by
  let tagged := inrRealizer .unit (by decide) left right hw (by omega)
  have bounded := (inr_names left right hw (by omega)).buffers
  change tagged.code.memBound ≤ 3 at bounded
  have retained := (Retain.code_names tagged.code (max 2 tagged.code.memBound)
    right.encoding.words (1 + max left.encoding.words right.encoding.words) saved.encoding.words
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)).2
  change (mergeRight left right saved hw fits).code.memBound ≤ _ at retained
  exact retained.trans (by change max 2 tagged.code.memBound + 1 ≤ 4; omega)

theorem merge_buffers : (merge left right saved hw fits).code.memBound ≤ 4 := by
  have one := mergeLeft_buffers left right saved hw fits
  have two := mergeRight_buffers left right saved hw fits
  change (Dispatch.code _ _ _ _).memBound ≤ 4
  exact (Dispatch.buffers _ _ _ _).trans (by omega)

end Signatures.Runtime.CaliperBackend.SumContext
