import Proofs.Runtime.Caliper.SchnorrROMPrivateGrowth
import Proofs.Runtime.Caliper.SchnorrROMPassBounds

/-! A complete ROM pass adds at most two saved cells per caller query and one
for the final LIVE hash. These are derived postconditions, including cutoff,
and apply to the same executions as the pass's time and memory bounds. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A B U P : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (ops : Handler.Operations config)

theorem Handler.tape_lengths (value : Handler.Input config) (valid : Handler.ready config value)
    (answer : Handler.Output config) (reached : answer ∈ support (Handler.source config ops value)) :
    (Handler.observed config answer).2.2.1.length ≤ (Handler.initialStore config value).2.1.length + 3 ∧
      (Handler.observed config answer).2.2.2.length ≤ (Handler.initialStore config value).2.2.length := by
  rcases value with (value | value) | value
  · simp only [Handler.source, Sum.elim, Handler.randomSource, support_map, Set.mem_image] at reached
    obtain ⟨read, supported, rfl⟩ := reached
    have growth := Random.tape_lengths config value read supported
    change read.val.2.2.1.length ≤ value.val.2.2.1.length + 3 ∧
      read.val.2.2.2.length ≤ value.val.2.2.2.length
    exact ⟨growth.1.trans (by omega), growth.2⟩
  · simp only [Handler.source, Sum.elim, Handler.hashSource, support_map, Set.mem_image] at reached
    obtain ⟨read, supported, rfl⟩ := reached
    have growth := Hash.tape_lengths config value valid read supported
    change read.val.2.2.1.length ≤ value.val.2.2.1.length + 3 ∧
      read.val.2.2.2.length ≤ value.val.2.2.2.length
    exact ⟨growth.1.trans (by omega), growth.2⟩
  · simp only [Handler.source, Sum.elim, Handler.signingSource, support_map, Set.mem_image] at reached
    obtain ⟨read, supported, rfl⟩ := reached
    exact ops.signing.tape_lengths value valid read supported

theorem CallerHandler.tape_lengths (value : CallerPackets.Packet config) (valid : CallerPackets.ready config value)
    (answer : CallerPackets.Reply config × config.handler.store.Value)
    (reached : answer ∈ support (CallerHandler.source config ops value)) :
    answer.2.val.2.1.length ≤ value.2.val.2.1.length + 3 ∧
      answer.2.val.2.2.length ≤ value.2.val.2.2.length := by
  simp only [CallerHandler.source, dite_eq_left valid, support_map, Set.mem_image] at reached
  obtain ⟨result, supported, rfl⟩ := reached
  have growth := Handler.tape_lengths config ops (CallerPackets.serviceRequest config value valid)
    (CallerPackets.service_ready config value valid) result supported
  rw [← CallerHandler.observed_finished, CallerPackets.service_store] at growth
  exact growth

theorem Caller.tape_lengths (routines : Caller.Routines config A B U) (fuel : Nat)
    (value : CallerControl.Packet A (CallerPackets.Request config) B config.handler.store.Value)
    (room : Handler.Reserved config fuel value.2.val) (answer)
    (reached : answer ∈ support (CallerControl.start routines.advance (CallerHandler.source config ops) fuel value)) :
    answer.2.val.2.1.length ≤ value.2.val.2.1.length + 3 * fuel ∧
      answer.2.val.2.2.length ≤ value.2.val.2.2.length := by
  have bounded := CallerControl.start_store routines.advance (CallerHandler.source config ops)
    (fun remaining saved => Handler.Reserved config remaining saved.val ∧
      saved.val.2.1.length + 3 * remaining ≤ value.2.val.2.1.length + 3 * fuel ∧
      saved.val.2.2.length ≤ value.2.val.2.2.length)
    (by
      intro small large saved fewer valid
      rcases valid with ⟨⟨managed, live, tape⟩, growth, replay⟩
      dsimp only [Handler.Reserved]
      exact ⟨⟨by omega, by omega, by omega⟩, by omega, replay⟩)
    (by
      intro remaining query saved valid reply supported
      have next := CallerHandler.reserved_after config ops remaining (query, saved) valid.1 reply supported
      have growth := CallerHandler.tape_lengths config ops (query, saved)
        (CallerPackets.reserved_ready config remaining (query, saved) valid.1) reply supported
      exact ⟨next.2, by dsimp only at growth; omega, growth.2.trans valid.2.2⟩)
    fuel value ⟨room, le_rfl, le_rfl⟩ answer reached
  simpa only [Nat.mul_zero, Nat.add_zero] using bounded.2

omit [SMul F G] [Sub G] in
theorem Terminal.tape_lengths (value : Terminal.Input config (P := P)) (valid : Terminal.ready config value)
    (answer : Terminal.Output config) (reached : answer ∈ support (Terminal.source config value)) :
    answer.2.val.2.1.length ≤ value.2.val.2.1.length + 1 ∧
      answer.2.val.2.2.length ≤ value.2.val.2.2.length := by
  rcases value with ⟨forge | next, saved⟩
  · simp only [Terminal.source, Terminal.successSource, support_map, Set.mem_image] at reached
    obtain ⟨hashed, supported, rfl⟩ := reached
    exact (ForgeryHash.growth config (forge, saved) valid hashed supported).2
  · simp only [Terminal.source, support_pure, Set.mem_singleton_iff] at reached
    subst answer
    exact ⟨Nat.le_succ _, le_rfl⟩

namespace Pass
variable (caller : Pass.Caller config A)

theorem finish_tape_lengths (fuel : Nat) (value : config.point.Value × config.handler.store.Value)
    (room : Caller.admitted config fuel value) (answer)
    (reached : answer ∈ support (finishSource config caller ops fuel value)) :
    answer.2.val.2.1.length ≤ value.2.val.2.1.length + (3 * fuel + 1) ∧
      answer.2.val.2.2.length ≤ value.2.val.2.2.length := by
  simp only [finishSource, support_bind, Set.mem_iUnion] at reached
  obtain ⟨packet, supported, finished⟩ := reached
  have calls := Caller.tape_lengths config ops (caller.routines config) fuel
    (caller.initial value.1, value.2) room packet supported
  have terminal := Terminal.tape_lengths config packet (called_ready config caller ops fuel value room packet supported)
    answer finished
  exact ⟨by dsimp only at calls; omega, terminal.2.trans calls.2⟩

theorem tape_lengths (fuel : Nat) (value : Initialization.Input config) (room : Initialization.admitted config fuel value)
    (answer) (reached : answer ∈ support (source config caller ops fuel value)) :
    answer.2.val.2.1.length ≤ value.1.val.1.length + (3 * fuel + 1) ∧
      answer.2.val.2.2.length ≤ value.1.val.2.length :=
  finish_tape_lengths config ops caller fuel (Initialization.start config value)
    (Initialization.reserved config fuel value room) answer reached

theorem execution_tape_lengths (fuel : Nat) (tape : RandomTape w) (value : Initialization.Input config)
    (room : Initialization.admitted config fuel value) (before : State w) (holds : (Initialization.input config).Holds value before)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program config caller ops fuel).execute (Fresh.port config.handler.sampler.tape) .unit tape before)) :
    ∃ answer, (output config caller).Holds answer finished.state ∧
      answer.2.val.2.1.length ≤ value.1.val.1.length + (3 * fuel + 1) ∧
      answer.2.val.2.2.length ≤ value.1.val.2.length ∧
      WordIO.Exec .unit tape ((program config caller ops fuel).lower (Fresh.port config.handler.sampler.tape))
        before finished.state finished.trace finished.time finished.net finished.peak := by
  obtain ⟨answer, supported, actual, equal, output, _, execution⟩ :=
    (refines config caller ops fuel tape value room before holds).right_support reached
  cases Option.some.inj equal
  have growth := tape_lengths config ops caller fuel value room answer supported
  exact ⟨answer, output, growth.1, growth.2, execution⟩

end Pass
end Signatures.Runtime.CaliperBackend.SchnorrROM
