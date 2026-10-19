import Signatures.Runtime.Caliper.CoronCache
import Signatures.Runtime.Caliper.CoronResponseMemory
import Signatures.Runtime.Caliper.BLSCallerInvariant

/-! Shared cache, response and caller-packet layouts for the Coron service.
The two reply logs have their own capacity and remain charged stored data. -/
namespace Signatures.Runtime.CaliperBackend.CoronService
open Caliper BoundedSource OracleComp OracleSpec

structure Layouts (w : Nat) (M F G : Type) (randomBound : Nat) (qS : Fin (randomBound + 1)) where
  cache : CacheLayout w M F
  point : Layout w G
  randomFits : randomBound + 1 ≤ 2 ^ w
  responseFits : 16 * (cache.value.representation.encoding.words + point.representation.encoding.words + 1) < 2 ^ w
  pairFits : cache.coinStorageWords < 2 ^ w
  capacityPred : Nat
  countFits : capacityPred + 1 < 2 ^ w
  serviceFits : 16 * ((cache.coinValues randomBound randomFits qS pairFits).lookup.width +
    4 * point.representation.encoding.words +
    2 * (1 + (capacityPred + 1) * (cache.key.representation.encoding.words + point.representation.encoding.words))) < 2 ^ w

namespace Layouts
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G : Type}
    (layout : Layouts w M F G randomBound qS)

def response : CoronResponse.Layouts w F G qS.val where
  scalar := layout.cache.value
  point := layout.point
  wordFits := layout.cache.wordFits
  coinFits := by have := layout.randomFits; have := qS.isLt; omega
  storageFits := layout.responseFits

def service : BLSReply.Layouts w M (F × Fin (qS.val + 1)) (G × (G × G)) G where
  cache := layout.cache.coinValues randomBound layout.randomFits qS layout.pairFits
  point := layout.point
  config := layout.response.config
  capacityPred := layout.capacityPred
  countFits := layout.countFits
  storageFits := by
    have room := layout.serviceFits
    change 16 * ((layout.cache.coinValues randomBound layout.randomFits qS layout.pairFits).lookup.width +
      layout.response.config.representation.encoding.words + layout.point.representation.encoding.words +
      2 * (1 + (layout.capacityPred + 1) * (layout.cache.key.representation.encoding.words + layout.point.representation.encoding.words))) < 2 ^ w
    rw [CoronResponse.Layouts.config_words]
    change 16 * (_ + 3 * layout.point.representation.encoding.words + layout.point.representation.encoding.words + _) < _
    omega

def port : Interactive.Port w unifSpec := UniformQuery.port randomBound layout.cache.wordFits layout.randomFits
def pairDefault (default : layout.cache.value.Value) : layout.service.cache.value.Value :=
  ⟨(default.val, 0), default.property, trivial⟩

variable [DecidableEq M]
def input (default : layout.cache.value.Value) : Layout w (BLSCallerPackets.Packet layout.service randomBound) where
  valid := BLSCallerPackets.ready layout.service (layout.pairDefault default) randomBound
  representation := BLSCallerHandler.admitted layout.service (layout.pairDefault default) randomBound layout.randomFits
def output : Layout w (BLSCallerPackets.Reply layout.service randomBound × layout.service.store.Value) :=
  Layout.all (BLSCallerPackets.output layout.service randomBound layout.randomFits)

end Layouts

variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G : Type}
    (layout : Layouts w M F G randomBound qS)

structure Routines [SMul F G] [Add G] [Zero G] where
  scale : Implementation .unit layout.response.scaleArgs layout.point (fun value => value.1 • value.2)
  add : Implementation .unit layout.response.points layout.point (fun value => value.1 + value.2)
  zeroValid : layout.point.valid 0
  scaleTime : Nat
  scaleWords : Nat
  addTime : Nat
  addWords : Nat
  scaleBound : scale.BoundedBy scaleTime scaleWords
  addBound : add.BoundedBy addTime addWords
  slots : Nat
  scaleNames : NamesBound scale.program.code slots
  addNames : NamesBound add.program.code slots
  reserve : slots + 5 < 2 ^ w

structure Sampler [SampleableType F] where
  code : Interactive.Code w
  source : ProbComp layout.cache.value.Value
  correct : Interactive.Refines layout.port .unit layout.cache.lookup.unit.representation layout.cache.value.representation (fun _ => source) code
  law : Subtype.val <$> source = ($ᵗ F : ProbComp F)
  time : Nat
  words : Nat
  slots : Nat
  timeBound : Interactive.TimeBound layout.port .unit layout.cache.lookup.unit.representation code time
  codeBound : (code.lower layout.port).descriptionWords ≤ words
  names : WordIO.NamesBound (code.lower layout.port) slots
  descriptionFits : (code.lower layout.port).DescriptionFits
  reserve : slots + 1 < 2 ^ w

end Signatures.Runtime.CaliperBackend.CoronService
