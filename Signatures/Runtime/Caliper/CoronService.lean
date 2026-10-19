import Signatures.Runtime.Caliper.CoronServiceLayout

/-! The complete random/hash/sign caller service, constructed from actual
scalar sampling and group routines. Tags, cache access, both logs and every
retained caller/service frame are part of the generated Caliper code. -/
namespace Signatures.Runtime.CaliperBackend.CoronService
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G : Type}
    (layout : Layouts w M F G randomBound qS)

namespace Routines
variable [SMul F G] [Add G] [Zero G] (routines : Routines layout)

def response (signing : Bool) : Implementation .unit layout.service.responseInput layout.point (CoronResponse.replyValue signing) :=
  CoronResponse.reply layout.response routines.zeroValid routines.scale routines.add routines.scaleNames.buffers
    (by have := routines.reserve; omega) signing
theorem response_buffers (signing : Bool) : (routines.response layout signing).program.code.memBound ≤ max 3 routines.slots + 1 :=
  CoronResponse.reply_buffers layout.response routines.zeroValid routines.scale routines.scaleNames.buffers
    (by have := routines.reserve; omega) routines.add routines.addNames.buffers signing
theorem response_reserve : (max 3 routines.slots + 1) + 3 < 2 ^ w := by
  have := routines.reserve; have := layout.cache.wordFits; omega
def responseTime (signing : Bool) : Nat := CoronResponse.timeBudget layout.response signing routines.scaleTime routines.addTime
def responseWords (signing : Bool) : Nat := CoronResponse.codeBudget layout.response signing routines.scaleWords routines.addWords
theorem response_bounded (signing : Bool) :
    (routines.response layout signing).BoundedBy (routines.responseTime layout signing) (routines.responseWords layout signing) :=
  CoronResponse.reply_bounded layout.response routines.zeroValid routines.scale routines.scaleBound routines.scaleNames.buffers
    (by have := routines.reserve; omega) routines.add routines.addBound signing
theorem response_names (signing : Bool) : NamesAccounted (routines.response layout signing).program.code routines.slots :=
  CoronResponse.reply_names layout.response routines.slots routines.zeroValid routines.scale routines.scaleNames.accounted
    routines.scaleNames.buffers (by have := routines.reserve; omega) routines.add routines.addNames.accounted signing
end Routines

namespace Sampler
variable [SampleableType F] (sampler : Sampler layout)
def pairCode : Interactive.Code w :=
  CoronSampling.code layout.cache.value randomBound layout.cache.wordFits layout.randomFits qS layout.cache.coinValueFits sampler.code
def pairSource : ProbComp layout.service.cache.value.Value :=
  CoronSampling.source layout.cache.value randomBound layout.cache.wordFits layout.randomFits qS layout.cache.coinValueFits sampler.source
theorem pair_correct : Interactive.Refines layout.port .unit layout.service.cache.lookup.unit.representation
    layout.service.cache.value.representation (fun _ => sampler.pairSource layout) (sampler.pairCode layout) :=
  CoronSampling.refines layout.cache.value randomBound layout.cache.wordFits layout.randomFits qS layout.cache.coinValueFits sampler.correct
theorem pair_law : Subtype.val <$> sampler.pairSource layout = ($ᵗ (F × Fin (qS.val + 1)) : ProbComp _) :=
  CoronSampling.uniform layout.cache.value randomBound layout.cache.wordFits layout.randomFits qS layout.cache.coinValueFits sampler.law
def pairTime : Nat := CoronSampling.timeBudget layout.cache.value sampler.time
def pairWords : Nat := CoronSampling.codeBudget layout.cache.value sampler.words
theorem pair_time : Interactive.TimeBound layout.port .unit layout.service.cache.lookup.unit.representation
    (sampler.pairCode layout) (sampler.pairTime layout) :=
  CoronSampling.time_bound layout.cache.value randomBound layout.cache.wordFits layout.randomFits qS layout.cache.coinValueFits
    sampler.correct sampler.timeBound
theorem pair_words : ((sampler.pairCode layout).lower layout.port).descriptionWords ≤ sampler.pairWords layout :=
  CoronSampling.code_words layout.cache.value randomBound layout.cache.wordFits layout.randomFits qS layout.cache.coinValueFits sampler.codeBound
theorem pair_names : WordIO.NamesBound ((sampler.pairCode layout).lower layout.port) (max 4 sampler.slots) :=
  CoronSampling.names layout.cache.value randomBound layout.cache.wordFits layout.randomFits qS layout.cache.coinValueFits sampler.names
theorem pair_fits : ((sampler.pairCode layout).lower layout.port).DescriptionFits :=
  CoronSampling.descriptionFits layout.cache.value randomBound layout.cache.wordFits layout.randomFits qS layout.cache.coinValueFits sampler.descriptionFits
theorem pair_reserve : max 4 sampler.slots + 1 < 2 ^ w := by
  have := sampler.reserve; have := layout.cache.wordFits; omega
end Sampler

variable [DecidableEq M] [SampleableType F] [SMul F G] [Add G] [Zero G]
    (default : layout.cache.value.Value) (routines : Routines layout) (sampler : Sampler layout)

def code : Interactive.Code w :=
  BLSCallerHandler.code (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    layout.service (layout.pairDefault default) randomBound layout.randomFits
    (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
    (routines.response layout) (routines.response_buffers layout) (routines.response_reserve layout) (sampler.pairCode layout)

def denote (value : BLSCallerPackets.Packet layout.service randomBound) :
    ProbComp (BLSCallerPackets.Reply layout.service randomBound × layout.service.store.Value) :=
  BLSCallerHandler.denote (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    layout.service (layout.pairDefault default) randomBound
    (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
    (routines.response layout) (routines.response_buffers layout) (routines.response_reserve layout) (sampler.pairSource layout) value

theorem refines : Interactive.RefinesOn (BLSCallerPackets.ready layout.service (layout.pairDefault default) randomBound)
    layout.port .unit (BLSCallerPackets.input layout.service randomBound layout.randomFits)
    (BLSCallerPackets.output layout.service randomBound layout.randomFits)
    (denote layout default routines sampler) (code layout default routines sampler) :=
  BLSCallerHandler.refines (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    layout.service (layout.pairDefault default) randomBound layout.randomFits
    (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
    (routines.response layout) (routines.response_buffers layout) (routines.response_reserve layout) (sampler.pairCode layout)
    (sampler.pair_correct layout)

end Signatures.Runtime.CaliperBackend.CoronService
