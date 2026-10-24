import Proofs.Runtime.Caliper.CoronFullBounds

/-! The whole generated program implements the paired Coron reduction from
empty private storage. The source machine certificate excludes cutoff; the
literal Caliper program and its complete resource ledger are the witness. -/
namespace Signatures.Runtime.CaliperBackend.CoronFull
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G A U V : Type}
    [DecidableEq M] [Field F] [SampleableType F] [AddCommGroup G] [Module F G]
    (service : CoronService.Layouts w M F G randomBound qS) (layout : CoronCaller.Layouts service A U)
    (default : service.cache.value.Value) (routines : CoronService.Routines service)
    (sampler : CoronService.Sampler service) (arithmetic : CoronTerminal.Arithmetic service)
    (caller : CoronCaller.Caller layout) (fuel : Nat) (fallback : service.point.Value)
    (invariant : CoronCaller.Caller.Invariant layout caller fuel)
    (witness : CoronCaller.Caller.Correspondence layout caller invariant V)
    (cacheRoom : fuel + 1 ≤ service.service.cache.capacityPred + 1) (logRoom : fuel ≤ service.service.capacityPred + 1)

include cacheRoom logRoom in
theorem source_eq (value : (challenge service layout).Value) :
    Subtype.val <$> denote service layout default routines sampler arithmetic caller fuel fallback value =
      Coron.Paired.reduction (F := F) (M := M) (qS := qS.val) value.val.2.val.1 value.val.2.val.2.1 value.val.2.val.2.2
        ((Subtype.val <$> witness.source (witness.inputView value.val.1)) : OracleComp (BLS.ROM.advSpec M G) (M × G)) := by
  change Subtype.val <$> CoronCaller.denote service layout default routines sampler arithmetic caller fuel fallback (start service layout value) = _
  rw [CoronCaller.source_eq service layout default routines sampler arithmetic caller fuel fallback invariant witness
    (start service layout value) (start_ready service layout fuel cacheRoom logRoom value), Coron.Paired.reduction_finish]
  rfl

include default fallback cacheRoom logRoom in
theorem within_source (bounded : CoronCaller.Caller.Bounds layout caller) (addresses : CoronCaller.addressBound service routines sampler) :
    Interactive.Within service.port (challenge service layout) service.point
      (codeBudget service layout routines sampler arithmetic caller bounded fuel)
      (memoryBudget service layout routines sampler arithmetic caller bounded fuel)
      (timeBudget service layout routines sampler arithmetic caller bounded fuel)
      (fun value => Coron.Paired.reduction (F := F) (M := M) (qS := qS.val) value.val.2.val.1 value.val.2.val.2.1 value.val.2.val.2.2
        ((Subtype.val <$> witness.source (witness.inputView value.val.1)) : OracleComp (BLS.ROM.advSpec M G) (M × G))) :=
  (within service layout default routines sampler arithmetic caller bounded fuel fallback invariant cacheRoom logRoom addresses).congr
    (source_eq service layout default routines sampler arithmetic caller fuel fallback invariant witness cacheRoom logRoom)

variable (keyGenerator : V) (adversary : BLS.ROM.AdversaryPK M G V)
    (same : ∀ input, Subtype.val <$> witness.source (witness.inputView input) = adversary (witness.inputView input))

include cacheRoom logRoom same in
theorem source_original (value : (challenge service layout).Value) :
    Subtype.val <$> denote service layout default routines sampler arithmetic caller fuel fallback value =
      BLS.CoCDH.coronReductionLazyPK (F := F) qS.val (BLS.ROM.cacheForgeryPK adversary)
        value.val.2.val.1 keyGenerator value.val.2.val.2.1 (witness.inputView value.val.1) value.val.2.val.2.2 := by
  rw [source_eq service layout default routines sampler arithmetic caller fuel fallback invariant witness cacheRoom logRoom, same]
  exact Coron.Paired.reduction_original _ _ _ keyGenerator _ adversary

include default fallback cacheRoom logRoom same in
theorem within_original (bounded : CoronCaller.Caller.Bounds layout caller) (addresses : CoronCaller.addressBound service routines sampler) :
    Interactive.Within service.port (challenge service layout) service.point
      (codeBudget service layout routines sampler arithmetic caller bounded fuel)
      (memoryBudget service layout routines sampler arithmetic caller bounded fuel)
      (timeBudget service layout routines sampler arithmetic caller bounded fuel)
      (fun value => BLS.CoCDH.coronReductionLazyPK (F := F) qS.val (BLS.ROM.cacheForgeryPK adversary)
        value.val.2.val.1 keyGenerator value.val.2.val.2.1 (witness.inputView value.val.1) value.val.2.val.2.2) :=
  (within service layout default routines sampler arithmetic caller bounded fuel fallback invariant cacheRoom logRoom addresses).congr
    (source_original service layout default routines sampler arithmetic caller fuel fallback invariant witness cacheRoom logRoom
      keyGenerator adversary same)

end Signatures.Runtime.CaliperBackend.CoronFull
