import Signatures.Runtime.Caliper.BLSAccumulateSource
import Signatures.Runtime.Caliper.BLSCachePairs
import Signatures.Runtime.Caliper.CacheAccumulateMemory

/-! Shared scalar layout for BLS private extraction reads. Both variants use
the same represented field and scalar primitives; the bad variant enlarges the
cache payload to a pair and charges that storage explicitly. -/
namespace Signatures.Runtime.CaliperBackend.BLSPrivateAccumulate
open Caliper BoundedSource

structure Layouts (w : Nat) (M F : Type) where
  cache : CacheLayout w M F
  pairStorageFits : cache.pairStorageWords < 2 ^ w
  scalarStorageFits : 32 * cache.value.representation.encoding.words < 2 ^ w
  goodStorageFits : 16 * (cache.lookup.width + cache.value.representation.encoding.words +
    cache.value.representation.encoding.words) < 2 ^ w
  badStorageFits : 16 * ((cache.pairValues pairStorageFits).lookup.width + cache.value.representation.encoding.words +
    (cache.pairValues pairStorageFits).value.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {M F : Type} (layout : Layouts w M F)
def arithmetic : BLSAccumulate.Layouts w F := ⟨layout.cache.value, layout.cache.wordFits, layout.scalarStorageFits⟩
def good : CacheAccumulate.Layouts w M F F := ⟨layout.cache, layout.cache.value, layout.goodStorageFits⟩
def bad : CacheAccumulate.Layouts w M F (F × F) :=
  ⟨layout.cache.pairValues layout.pairStorageFits, layout.cache.value, layout.badStorageFits⟩
end Layouts

variable {w : Nat} {M F : Type} [Mul F] [Add F] (layout : Layouts w M F)
    (mul : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 * value.2))
    (add : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)
    (addBuffers : add.program.code.memBound ≤ slots)

def goodUpdate : Implementation .unit layout.good.combine layout.good.cache.value
    (fun value => value.2.2 + value.1 * value.2.1) := BLSAccumulate.good layout.arithmetic mul add mulBuffers reserve
def badUpdate : Implementation .unit layout.bad.combine layout.bad.cache.value
    (fun value => (value.2.2.1 + value.1 * value.2.1.1, value.2.2.2 + value.1 * value.2.1.2)) :=
  BLSAccumulate.bad layout.arithmetic mul add mulBuffers reserve addBuffers
include addBuffers in
theorem goodUpdate_buffers : (goodUpdate layout mul add mulBuffers reserve).program.code.memBound ≤ max 3 slots + 1 :=
  BLSAccumulate.good_buffers layout.arithmetic mul add mulBuffers reserve addBuffers
theorem badUpdate_buffers : (badUpdate layout mul add mulBuffers reserve addBuffers).program.code.memBound ≤ max 3 slots + 2 :=
  BLSAccumulate.bad_buffers layout.arithmetic mul add mulBuffers reserve addBuffers
include layout reserve in
omit [Mul F] [Add F] in
theorem good_reserve : (max 3 slots + 1) + 2 < 2 ^ w := by have := layout.cache.wordFits; omega
include layout reserve in
omit [Mul F] [Add F] in
theorem bad_reserve : (max 3 slots + 2) + 2 < 2 ^ w := by have := layout.cache.wordFits; omega

end Signatures.Runtime.CaliperBackend.BLSPrivateAccumulate
