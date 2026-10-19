import Signatures.Runtime.Caliper.CoronService

/-! Joint source semantics and capacity preservation for the executed Coron
service. The native-state projection is a proof view; the real code retains
the paired cache and both reply logs, all charged by CoronServiceBounds. -/
namespace Signatures.Runtime.CaliperBackend.CoronService
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G : Type}
    [DecidableEq M] [SampleableType F] [SMul F G] [Add G] [Zero G]
    (layout : Layouts w M F G randomBound qS) (default : layout.cache.value.Value)
    (routines : Routines layout) (sampler : Sampler layout)

theorem denote_source (value : (layout.input default).Value) :
    BLSCallerHandler.observed layout.service randomBound <$> denote layout default routines sampler value.val =
      (fun out => (BLSCallerHandler.answer layout.service randomBound value.val.1 out.1, out.2)) <$>
        ((BLSCallerHandler.original (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
          CoronResponse.replyValue)
          (BLSCallerHandler.query layout.service randomBound value.val.1)).run value.val.2.val :=
  BLSCallerHandler.denote_source (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    layout.service (layout.pairDefault default) randomBound
    (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
    (routines.response layout) (routines.response_buffers layout) (routines.response_reserve layout)
    (sampler.pairSource layout) (sampler.pair_law layout) value.val value.property

omit [SampleableType F] [SMul F G] [Add G] [Zero G] in
theorem ready_of_reserved (value : BLSCallerPackets.Packet layout.service randomBound) {remaining : Nat}
    (reserved : BLSReply.Reserved layout.service (remaining + 1) value.2.val) :
    (layout.input default).valid value :=
  BLSCallerHandler.ready_of_reserved layout.service (layout.pairDefault default) randomBound value reserved

theorem reserved_after (value : BLSCallerPackets.Packet layout.service randomBound) {remaining : Nat}
    (reserved : BLSReply.Reserved layout.service (remaining + 1) value.2.val)
    (reply : BLSCallerPackets.Reply layout.service randomBound × layout.service.store.Value)
    (supported : reply ∈ support (denote layout default routines sampler value)) :
    BLSReply.Reserved layout.service remaining reply.2.val :=
  BLSCallerHandler.reserved_after (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    layout.service (layout.pairDefault default) randomBound
    (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
    (routines.response layout) (routines.response_buffers layout) (routines.response_reserve layout)
    (sampler.pairSource layout) (sampler.pair_law layout) value reserved reply supported

end Signatures.Runtime.CaliperBackend.CoronService

namespace Signatures.Runtime.CaliperBackend.CoronService
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G : Type}
    [DecidableEq M] [Field F] [SampleableType F] [AddCommGroup G] [Module F G]
    (layout : Layouts w M F G randomBound qS) (default : layout.cache.value.Value)
    (routines : Routines layout) (sampler : Sampler layout)

/-- Includes the random reply's range, all three challenge points and both
original native caches. The signing set is projected from the stored log. -/
def nativeObserved (value : BLSCallerPackets.Reply layout.service randomBound × layout.service.store.Value) :
    ((Nat × Nat) ⊕ G) × (G × (G × G)) × Coron.NativeState F M qS.val :=
  (BLSCallerHandler.replyValue layout.service randomBound value.1, value.2.val.1,
    Coron.Paired.nativeState value.2.val.2)

theorem denote_native (value : (layout.input default).Value) :
    nativeObserved layout <$> denote layout default routines sampler value.val =
      (fun out => (BLSCallerHandler.answer layout.service randomBound value.val.1 out.1, value.val.2.val.1, out.2)) <$>
        ((Coron.nativeOracle value.val.2.val.1.1 value.val.2.val.1.2.1 value.val.2.val.1.2.2 qS.val)
          (BLSCallerHandler.query layout.service randomBound value.val.1)).run
            (Coron.Paired.nativeState value.val.2.val.2) := by
  have source := congrArg (fun computation =>
    (fun out : ((Nat × Nat) ⊕ G) × BLSReply.Store M (F × Fin (qS.val + 1)) (G × (G × G)) G =>
      (out.1, out.2.1, Coron.Paired.nativeState out.2.2)) <$> computation)
    (denote_source layout default routines sampler value)
  have native := congrArg (fun computation =>
    (fun out => (BLSCallerHandler.answer layout.service randomBound value.val.1 out.1, value.val.2.val.1, out.2)) <$> computation)
    (Coron.Paired.oracle_native value.val.2.val.1.1 value.val.2.val.1.2.1 value.val.2.val.1.2.2
      (BLSCallerHandler.query layout.service randomBound value.val.1) value.val.2.val.2)
  simp only [Functor.map_map] at source
  exact source.trans (by simpa only [BLSCallerHandler.original, Coron.Paired.oracle, StateT.run, Functor.map_map,
    Prod.map, id_eq, CoronResponse.reply_source] using native)

end Signatures.Runtime.CaliperBackend.CoronService
