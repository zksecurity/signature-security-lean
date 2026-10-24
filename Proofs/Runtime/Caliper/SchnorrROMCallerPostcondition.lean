import Proofs.Runtime.Caliper.SchnorrROMCaller
import Proofs.Runtime.Caliper.CallerPostcondition

/-! Every supported exit retains public configuration and space for the final
LIVE hash, including immediate return, early return and observable fuel cutoff. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Caller
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A B U : Type} (config : Signing.Enumerated.Configuration w M F G)

structure Postcondition (before after : config.handler.store.Value) : Prop where
  reserved : Handler.Reserved config 0 after.val
  config : after.val.1.1 = before.val.1.1

variable [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (routines : Routines config A B U) (ops : Handler.Operations config)

omit [SMul F G] [Sub G] in
theorem Postcondition.final_hash {before after : config.handler.store.Value} (post : Postcondition config before after) (key : M × G) :
    FinalHash.admissible config (key, after.val) ∧ after.val.2.1.length < config.sampler.capacity :=
  Handler.reserved_final config key after.val post.reserved

theorem start_postcondition (fuel : Nat)
    (value : CallerControl.Packet A (CallerPackets.Request config) B config.handler.store.Value)
    (room : Handler.Reserved config fuel value.2.val)
    (answer) (reached : answer ∈ support (CallerControl.start routines.advance (CallerHandler.source config ops) fuel value)) :
    Postcondition config value.2 answer.2 := by
  have preserved := CallerControl.start_store routines.advance (CallerHandler.source config ops)
    (fun remaining saved => Handler.Reserved config remaining saved.val ∧ saved.val.1.1 = value.2.val.1.1)
    (by
      intro small large saved fewer valid
      refine ⟨?_, valid.2⟩
      rcases valid.1 with ⟨managed, live, tape⟩
      dsimp only [Handler.Reserved]
      exact ⟨by omega, by omega, by omega⟩)
    (by
      intro remaining query saved valid reply supported
      have next := CallerHandler.reserved_after config ops remaining (query, saved) valid.1 reply supported
      exact ⟨next.2, next.1.trans valid.2⟩)
    fuel value ⟨room, rfl⟩ answer reached
  exact ⟨preserved.1, preserved.2⟩

theorem execution_postcondition (fuel : Nat) (tape : RandomTape w)
    (value : U × config.handler.store.Value) (room : admitted config fuel value)
    (before : State w) (holds : (routines.inputLayout config).Holds value before)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program config routines ops fuel).execute (Fresh.port config.handler.sampler.tape) .unit tape before)) :
    ∃ answer, (routines.outputLayout config).Holds answer finished.state ∧ Postcondition config value.2 answer.2 ∧
      WordIO.Exec .unit tape ((program config routines ops fuel).lower (Fresh.port config.handler.sampler.tape))
        before finished.state finished.trace finished.time finished.net finished.peak := by
  obtain ⟨answer, supported, actual, equal, output, _, execution⟩ :=
    (refines config routines ops fuel tape value room before holds).right_support reached
  cases Option.some.inj equal
  exact ⟨answer, output, start_postcondition config routines ops fuel (routines.initial value.1, value.2) room answer supported, execution⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.Caller
