import Proofs.Runtime.Caliper.CoronService

/-! Derived bounds for the complete Coron caller service. The witness contains
the sampler, cache, responses, transcripts, tags and retained frames. It charges
stored code and initial data as well as memory at every instruction boundary. -/
namespace Signatures.Runtime.CaliperBackend.CoronService
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G : Type}
    [DecidableEq M] [SampleableType F] [SMul F G] [Add G] [Zero G]
    (layout : Layouts w M F G randomBound qS) (default : layout.cache.value.Value)
    (routines : Routines layout) (sampler : Sampler layout)

def timeBudget : Nat :=
  BLSOracle.timeBudget layout.service
    (BLSDispatch.timeBudget (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
      layout.service (sampler.pairTime layout) (routines.responseTime layout)) +
      108 * BLSCallerPackets.width layout.service + 8

def codeBudget : Nat :=
  BLSOracle.codeBudget layout.service
    (BLSDispatch.codeBudget (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
      layout.service (sampler.pairWords layout) (routines.responseWords layout)) +
      710 * BLSCallerPackets.width layout.service + 420

def nameBudget : Nat := max (max 5 sampler.slots) routines.slots

def memoryBudget : Nat :=
  5 * codeBudget layout routines sampler + 4 * nameBudget layout routines sampler + 3 +
    (layout.input default).representation.encoding.words + timeBudget layout routines sampler

theorem time_bound : Interactive.TimeBoundOn
    (BLSCallerPackets.ready layout.service (layout.pairDefault default) randomBound)
    layout.port .unit (BLSCallerPackets.input layout.service randomBound layout.randomFits)
    (code layout default routines sampler) (timeBudget layout routines sampler) :=
  BLSCallerHandler.time (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    layout.service (layout.pairDefault default) randomBound layout.randomFits
    (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
    (routines.response layout) (routines.response_buffers layout) (routines.response_reserve layout)
    (sampler.pairCode layout) (sampler.pair_correct layout) (sampler.pair_time layout) (routines.response_bounded layout)

theorem code_words : ((code layout default routines sampler).lower layout.port).descriptionWords ≤
    codeBudget layout routines sampler :=
  BLSCallerHandler.words (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    layout.service (layout.pairDefault default) randomBound layout.randomFits
    (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
    (routines.response layout) (routines.response_buffers layout) (routines.response_reserve layout)
    (sampler.pairCode layout) (sampler.pair_words layout) (routines.response_bounded layout)

theorem names : WordIO.NamesAccounted ((code layout default routines sampler).lower layout.port)
    (nameBudget layout routines sampler) := by
  have bounded := BLSCallerHandler.names (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    layout.service (layout.pairDefault default) randomBound layout.randomFits
    (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
    (routines.response layout) (routines.response_buffers layout) (routines.response_reserve layout)
    (sampler.pairCode layout) (sampler.pair_names layout) (routines.response_names layout)
  exact bounded.mono (by unfold nameBudget; omega)

theorem descriptionFits : ((code layout default routines sampler).lower layout.port).DescriptionFits :=
  BLSCallerHandler.descriptionFits (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    layout.service (layout.pairDefault default) randomBound layout.randomFits
    (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
    (routines.response layout) (routines.response_buffers layout) (routines.response_reserve layout)
    (sampler.pairCode layout) (sampler.pair_fits layout) (sampler.pair_names layout) (sampler.pair_reserve layout)

/-- A single generated program handles every admitted random, hash or signing
request. Only scalar sampling and group primitives are supplied implementations. -/
theorem within : Interactive.Within layout.port (layout.input default) layout.output
    (codeBudget layout routines sampler) (memoryBudget layout default routines sampler)
    (timeBudget layout routines sampler) (fun value => denote layout default routines sampler value.val) := by
  have refined : Interactive.Refines layout.port .unit (layout.input default).representation
      (BLSCallerPackets.output layout.service randomBound layout.randomFits)
      (fun value => denote layout default routines sampler value.val) (code layout default routines sampler) :=
    fun tape value before holds => refines layout default routines sampler tape value.val value.property before holds
  have timed : Interactive.TimeBound layout.port .unit (layout.input default).representation
      (code layout default routines sampler) (timeBudget layout routines sampler) :=
    fun tape value before holds => time_bound layout default routines sampler tape value.val value.property before holds
  have bounded := Interactive.within_of_refines_accounted
    (refined.viewOutput layout.output.representation (fun value => ⟨value, trivial⟩) (fun _ => rfl))
    timed (code_words layout default routines sampler) (names layout default routines sampler)
    (descriptionFits layout default routines sampler)
  exact bounded.congr (fun _ => by rw [Functor.map_map]; exact id_map _)

end Signatures.Runtime.CaliperBackend.CoronService
