import Proofs.Runtime.Caliper.RowFoldMemory
import Proofs.Runtime.Caliper.BLSPrivateAccumulateOracle

/-! Scalar and pair row evaluators share the message, coefficient and point
encodings. Pair-cache storage and every row's point bytes are charged. -/
namespace Signatures.Runtime.CaliperBackend.BLSRows
open Caliper BoundedSource
structure Layouts (w : Nat) (M G F : Type) where
  accumulation : BLSPrivateAccumulate.Layouts w M F
  point : Layout w G
  goodStorageFits : 16 * (accumulation.good.width + point.representation.encoding.words) < 2 ^ w
  badStorageFits : 16 * (accumulation.bad.width + point.representation.encoding.words) < 2 ^ w
namespace Layouts
variable {w : Nat} {M G F : Type} (layout : Layouts w M G F)
def good : RowRequest.Layouts w M G F F := ⟨layout.accumulation.good, layout.point, layout.goodStorageFits⟩
def bad : RowRequest.Layouts w M G F (F × F) := ⟨layout.accumulation.bad, layout.point, layout.badStorageFits⟩
end Layouts
end Signatures.Runtime.CaliperBackend.BLSRows
