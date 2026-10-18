import Signatures.Runtime.Caliper.BLSOracleMemory
import Signatures.Runtime.Caliper.BLSOracleReady

/-! Full BLS AGM services assembled from scalar sampling and scale/add routines.
No finished handler implementation is supplied as a contract. -/

namespace Signatures.Runtime.CaliperBackend.BLSOracle
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G : Type}
    [DecidableEq (key.Value base)] [SMul (val.Value base) G]
    (layout : BLSReply.SchemeLayouts w (key.Value base) (val.Value base) G)
    (default : layout.cache.value.Value) (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (scalar : Interactive.Code w)
    (scale : Implementation .unit layout.response.scaleArgs layout.point (fun value => value.1 • value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 5 < 2 ^ w)

def goodCode : Interactive.Code w :=
  code layout.good default randomBound randomFits P comparison correct (BLSResponse.good layout.response scale)
    (BLSResponse.good_buffers layout.response scale scaleBuffers) (layout.goodReserve reserve) scalar

variable [Add G] (add : Implementation .unit layout.response.points layout.point (fun value => value.1 + value.2))
    (addBuffers : add.program.code.memBound ≤ slots)

def badCode : Interactive.Code w :=
  code (base := base) (key := key) (val := .pair val val) layout.bad (layout.pairDefault default) randomBound randomFits P comparison correct
    (BLSResponse.bad layout.response scale add scaleBuffers (by omega) addBuffers)
    (BLSResponse.bad_buffers layout.response scale add scaleBuffers (by omega) addBuffers) (layout.badReserve reserve)
    (BLSCache.pairSampler layout.cache (UniformQuery.port randomBound layout.cache.wordFits randomFits) scalar)

end Signatures.Runtime.CaliperBackend.BLSOracle
