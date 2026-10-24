import Proofs.Runtime.Caliper.CoronFullSource
import Proofs.Runtime.Caliper.CoronFullChallenges
import Proofs.Runtime.Caliper.WithinInput
import Proofs.Runtime.Caliper.CoCDH

/-! The complete constructed Coron reduction belongs to the fixed Caliper
co-CDH class. Reinterpreting its nested represented input as the raw challenge
preserves exactly the stored bytes; no executable conversion is omitted. -/
namespace Signatures.Runtime.CaliperBackend.CoronFull
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G K A : Type}
    [DecidableEq M] [Field F] [SampleableType F] [AddCommGroup G] [Module F G]
    [AddCommGroup K] [Module F K]
    (service : CoronService.Layouts w M F G randomBound qS) (key : Layout w K)
    (layout : CoronCaller.Layouts service A key.Value) (input_eq : layout.input = key.representation)
    (fits : key.representation.encoding.words + service.service.config.representation.encoding.words < 2 ^ w)
    (default : service.cache.value.Value) (routines : CoronService.Routines service)
    (sampler : CoronService.Sampler service) (arithmetic : CoronTerminal.Arithmetic service)
    (caller : CoronCaller.Caller layout) (bounded : CoronCaller.Caller.Bounds layout caller)
    (fuel : Nat) (fallback : service.point.Value)
    (invariant : CoronCaller.Caller.Invariant layout caller fuel)
    (witness : CoronCaller.Caller.Correspondence layout caller invariant K)
    (inputView : ∀ value, witness.inputView value = value.val)
    (cacheRoom : fuel + 1 ≤ service.service.cache.capacityPred + 1) (logRoom : fuel ≤ service.service.capacityPred + 1)
    (addresses : CoronCaller.addressBound service routines sampler)
    (scalarKeyFits : service.cache.value.representation.encoding.words + key.representation.encoding.words < 2 ^ w)
    (keyScale : Implementation .unit (service.cache.value.prod key scalarKeyFits) key (fun value => value.1 • value.2))
    (generator : service.point.Value) (keyGenerator : key.Value)
    (generates : Function.Surjective (fun scalar : F => scalar • generator.val))
    (adversary : BLS.ROM.AdversaryPK M G K)
    (same : ∀ input, Subtype.val <$> witness.source (witness.inputView input) = adversary (witness.inputView input))

include default fallback input_eq inputView cacheRoom logRoom addresses keyScale generates same in
theorem coCDH_within :
    coCDHWithin service.port (sourceChallenge service key fits) service.point generator.val keyGenerator.val
      (codeBudget service layout routines sampler arithmetic caller bounded fuel)
      (memoryBudget service layout routines sampler arithmetic caller bounded fuel)
      (timeBudget service layout routines sampler arithmetic caller bounded fuel)
      (BLS.CoCDH.coronReductionLazyPK (F := F) qS.val (BLS.ROM.cacheForgeryPK adversary)) := by
  refine ⟨challenge_valid service key fits sampler routines generator generates scalarKeyFits keyScale keyGenerator, ?_⟩
  let view : (sourceChallenge service key fits).Value → (challenge service layout).Value :=
    fun value => ⟨((productView key service.service.config) value), trivial⟩
  have encoded (value : (sourceChallenge service key fits).Value) :
      (challenge service layout).representation.encoding.encode (view value) =
        (sourceChallenge service key fits).representation.encoding.encode value := by
    change layout.input.encoding.encode ⟨value.val.1, value.property.1⟩ ++ _ =
      key.representation.encoding.encode ⟨value.val.1, value.property.1⟩ ++ _
    rw [input_eq]
    rfl
  have bounded := (within_original service layout default routines sampler arithmetic caller fuel fallback invariant witness
    cacheRoom logRoom keyGenerator.val adversary same bounded addresses).viewInput (sourceChallenge service key fits) view encoded
  exact bounded.congr (fun value => by
    change BLS.CoCDH.coronReductionLazyPK (F := F) qS.val (BLS.ROM.cacheForgeryPK adversary)
      value.val.2.1 keyGenerator.val value.val.2.2.1 (witness.inputView ⟨value.val.1, value.property.1⟩) value.val.2.2.2 = _
    rw [inputView])

end Signatures.Runtime.CaliperBackend.CoronFull
