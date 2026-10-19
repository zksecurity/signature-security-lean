import Signatures.Runtime.Caliper.BLSAccumulateNames

/-! Source-expression refinements for both extraction accumulators. The same
actual code and derived budgets implement goodCombine and badCombine. -/

namespace Signatures.Runtime.CaliperBackend.BLSAccumulate
open Caliper BoundedSource
variable {w : Nat} {F G₁ G₂ M : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq M]
    (layout : Layouts w F)
    (mul : Implementation .unit layout.pair layout.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.pair layout.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)
    (cost : PrimitiveCosts)

def goodSource : Implementation .unit layout.good layout.scalar
    (fun value => LazyAGM.goodCombine.denote (arithmetic F G₁ G₂ M M cost) (value.2.1, value.1, value.2.2, ())) :=
  (good layout mul add mulBuffers reserve).castFunction (by funext value; rfl)
variable (addBuffers : add.program.code.memBound ≤ slots)
def badSource : Implementation .unit layout.bad layout.pair
    (fun value => LazyAGM.badCombine.denote (arithmetic F G₁ G₂ M M cost) (value.2.1, value.1, value.2.2, ())) :=
  (bad layout mul add mulBuffers reserve addBuffers).castFunction (by funext value; rfl)

variable {mulTime mulCode addTime addCode : Nat}
    (mulBound : mul.BoundedBy mulTime mulCode) (addBound : add.BoundedBy addTime addCode)
include mulBound addBound in
theorem goodSource_bounded : (goodSource (G₁ := G₁) (G₂ := G₂) (M := M) layout mul add mulBuffers reserve cost).BoundedBy
    (goodTime layout mulTime addTime) (goodCode layout mulCode addCode) :=
  ⟨(good_bounded layout mul add mulBound addBound mulBuffers reserve).time_le,
    (good_bounded layout mul add mulBound addBound mulBuffers reserve).code_le⟩
include mulBound addBound in
theorem badSource_bounded : (badSource (G₁ := G₁) (G₂ := G₂) (M := M) layout mul add mulBuffers reserve cost addBuffers).BoundedBy
    (badTime layout mulTime addTime) (badCode layout mulCode addCode) :=
  ⟨(bad_bounded layout mul add mulBound addBound mulBuffers reserve addBuffers).time_le,
    (bad_bounded layout mul add mulBound addBound mulBuffers reserve addBuffers).code_le⟩

end Signatures.Runtime.CaliperBackend.BLSAccumulate
