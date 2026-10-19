import Signatures.Runtime.Caliper.CoronCallerBounds
import Signatures.Runtime.Caliper.CallerMachine

/-! The composed caller/extractor implements the original paired Coron oracle
and terminal source computation. Only local machine-head correspondence is
supplied; source termination rules out the generated controller's cutoff. -/
namespace Signatures.Runtime.CaliperBackend.CoronCaller
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G A U V : Type}
    {service : CoronService.Layouts w M F G randomBound qS} (layout : Layouts service A U)
    (caller : Caller layout) {fuel : Nat} (invariant : Caller.Invariant layout caller fuel)

structure Caller.Correspondence (V : Type) where
  machine : OracleMachine (Model.LazyAGM.advSpec M M G) V layout.Forgery
  stateView : layout.Request × A → machine.State
  inputView : U → V
  source : V → OracleComp (Model.LazyAGM.advSpec M M G) layout.Forgery
  implements : machine.ImplementsWithin source fuel
  advance : ∀ remaining q c, invariant.domain (remaining + 1) (q, c) →
    ∀ next : (Model.LazyAGM.advSpec M M G).Range (BLSCallerHandler.query service.service randomBound q) → machine.State,
      machine.view (stateView (q, c)) = .inr ⟨BLSCallerHandler.query service.service randomBound q, next⟩ →
      ∀ represented original, BLSCallerHandler.replyMatches service.service randomBound q represented original →
        CallerMachine.Matches machine (BLSCallerHandler.query service.service randomBound) stateView
          (caller.advance (c, represented)) (next original)
  initial : ∀ value, CallerMachine.Matches machine (BLSCallerHandler.query service.service randomBound) stateView
    (caller.initial value) (machine.init (inputView value))

variable [DecidableEq M] [Field F] [SampleableType F] [AddCommGroup G] [Module F G]
    (service : CoronService.Layouts w M F G randomBound qS) (layout : Layouts service A U)
    (default : service.cache.value.Value) (routines : CoronService.Routines service)
    (sampler : CoronService.Sampler service) (arithmetic : CoronTerminal.Arithmetic service)
    (caller : Caller layout) (fuel : Nat) (fallback : service.point.Value)
    (invariant : Caller.Invariant layout caller fuel) (witness : Caller.Correspondence layout caller invariant V)

theorem called_source (value : U × service.service.store.Value) (valid : layout.ready fuel value) :
    CallerMachine.observe Subtype.val <$> called service layout default routines sampler caller fuel value =
      (fun result => (some result.1, result.2)) <$>
        (simulateQ (BLSCallerHandler.original (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
          CoronResponse.replyValue) (witness.source (witness.inputView value.1))).run value.2.val :=
  CallerMachine.start_eq_simulateQ witness.machine (BLSCallerHandler.query service.service randomBound) witness.stateView
    Subtype.val (BLSCallerHandler.replyMatches service.service randomBound) caller.advance
    (CoronService.denote service default routines sampler)
    (BLSCallerHandler.original (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
      CoronResponse.replyValue)
    (BLSCaller.Invariant service.service randomBound invariant.domain)
    (fun _ packet valid => BLSCallerHandler.synchronizes
      (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
      service.service (service.pairDefault default) randomBound (CoronCache.primitives F M) CoronCache.comparison
      (CoronCache.comparison_correct F M) (routines.response service) (routines.response_buffers service)
      (routines.response_reserve service) (sampler.pairSource service) (sampler.pair_law service) (packet.1.1, packet.2)
      (BLSCallerHandler.ready_of_reserved service.service (service.pairDefault default) randomBound (packet.1.1, packet.2) valid.2))
    (fun remaining q c _ valid => witness.advance remaining q c valid.1)
    (BLSCaller.preserves (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
      service.service (service.pairDefault default) randomBound (CoronCache.primitives F M) CoronCache.comparison
      (CoronCache.comparison_correct F M) (routines.response service) (routines.response_buffers service)
      (routines.response_reserve service) (sampler.pairSource service) (sampler.pair_law service)
      invariant.domain caller.advance invariant.advance)
    fuel (caller.initial value.1, value.2) (witness.inputView value.1)
    (BLSCaller.initial_invariant (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
      service.service randomBound invariant.domain caller.initial fuel (layout.ready fuel)
      (fun value _ => invariant.initial value.1) (fun _ valid => layout.reserved valid) value valid)
    (witness.initial value.1) witness.source witness.implements

noncomputable def finishSource (value : Option layout.Forgery × BLSReply.Store M (F × Fin (qS.val + 1)) (G × (G × G)) G) : ProbComp G :=
  match value.1 with
  | none => pure fallback.val
  | some forgery => Coron.Paired.finish value.2.1.2.1 forgery.val value.2.2.1

theorem finish_source (value : layout.Packet) (valid : CoronCallerFinish.ready service default value) :
    Subtype.val <$> CoronCallerFinish.denote service default sampler arithmetic fallback value =
      finishSource service layout fallback (CallerMachine.observe Subtype.val value) := by
  rcases value with ⟨forgery | next, saved⟩
  · exact CoronCallerFinish.source_return service default sampler arithmetic fallback (forgery, saved) valid
  · exact CoronCallerFinish.source_cutoff service default sampler arithmetic fallback next saved

theorem denote_source (value : U × service.service.store.Value) (valid : layout.ready fuel value) :
    Subtype.val <$> denote service layout default routines sampler arithmetic caller fuel fallback value =
      ((simulateQ (BLSCallerHandler.original (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
        CoronResponse.replyValue) (witness.source (witness.inputView value.1))).run value.2.val >>=
          fun answer => Coron.Paired.finish answer.2.1.2.1 answer.1.val answer.2.2.1) := by
  have invoked := called_source service layout default routines sampler caller fuel invariant witness value valid
  have finished : Subtype.val <$> denote service layout default routines sampler arithmetic caller fuel fallback value =
      (called service layout default routines sampler caller fuel value >>= fun packet =>
        finishSource service layout fallback (CallerMachine.observe Subtype.val packet)) := by
    simp only [denote, map_bind]
    apply bind_congr_of_forall_mem_support
    intro packet reached
    exact finish_source service layout default sampler arithmetic fallback packet
      (called_ready service layout default routines sampler caller fuel value valid packet reached)
  rw [finished, ← bind_map_left, invoked, bind_map_left]
  rfl

theorem original_simulation {Y : Type} (configuration : G × (G × G))
    (program : OracleComp (BLS.ROM.advSpec M G) Y) (saved : Coron.Paired.State F M G qS.val) :
    (simulateQ (BLSCallerHandler.original (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
      CoronResponse.replyValue) program).run (configuration, saved) =
      (fun answer => (answer.1, configuration, answer.2)) <$>
        (simulateQ (Coron.Paired.oracle configuration.1 configuration.2.1 configuration.2.2) program).run saved := by
  have oracle_eq : BLSCallerHandler.original (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
      (CoronResponse.replyValue (F := F) (G := G) (qS := qS.val)) = fun q stored => (fun answer => (answer.1, stored.1, answer.2)) <$>
        (Coron.Paired.oracle stored.1.1 stored.1.2.1 stored.1.2.2 q).run stored.2 := by
    funext q stored
    simp only [BLSCallerHandler.original, Coron.Paired.oracle, CoronResponse.reply_source]
  induction program using OracleComp.inductionOn generalizing saved with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind q next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [oracle_eq, StateT.run, bind_map_left, map_bind]
    apply bind_congr
    rintro ⟨answer, nextStore⟩
    exact ih answer nextStore

theorem source_eq (value : U × service.service.store.Value) (valid : layout.ready fuel value) :
    Subtype.val <$> denote service layout default routines sampler arithmetic caller fuel fallback value =
      ((simulateQ (Coron.Paired.oracle value.2.val.1.1 value.2.val.1.2.1 value.2.val.1.2.2)
        (Subtype.val <$> witness.source (witness.inputView value.1))).run value.2.val.2 >>=
          fun answer => Coron.Paired.finish value.2.val.1.2.1 answer.1 answer.2.1) := by
  rw [denote_source service layout default routines sampler arithmetic caller fuel fallback invariant witness value valid,
    original_simulation]
  simp only [simulateQ_map, StateT.run_map, bind_map_left]

include default fallback in
theorem within_source (bounded : Caller.Bounds layout caller) (addresses : addressBound service routines sampler) :
    Interactive.Within service.port (layout.admitted fuel) service.point
      (codeBudget service layout routines sampler arithmetic caller bounded fuel)
      (memoryBudget service layout routines sampler arithmetic caller bounded fuel)
      (timeBudget service layout routines sampler arithmetic caller bounded fuel)
      (fun value => (simulateQ (Coron.Paired.oracle value.val.2.val.1.1 value.val.2.val.1.2.1 value.val.2.val.1.2.2)
        (Subtype.val <$> witness.source (witness.inputView value.val.1))).run value.val.2.val.2 >>=
          fun answer => Coron.Paired.finish value.val.2.val.1.2.1 answer.1 answer.2.1) :=
  (within service layout default routines sampler arithmetic caller bounded fuel fallback invariant addresses).congr
    (fun value => source_eq service layout default routines sampler arithmetic caller fuel fallback invariant witness value.val value.property)

end Signatures.Runtime.CaliperBackend.CoronCaller
