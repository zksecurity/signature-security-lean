import Signatures.Runtime.Caliper.SchnorrROMPassCallerBounds

/-! Connect the constructed caller and final hash to the original ROM pass.
Only local caller-step correspondence is supplied; the completed pass equation
is derived and preserves both caches and tapes jointly. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Pass
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
    [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Caller config A)

structure Caller.Source (fuel : Nat) where
  Input : Type
  machine : OracleMachine (FiatShamir.cmaOracleSpec M G F F) Input (ForgeryHash.forgery config).Value
  inputView : config.point.Value → Input
  stateView : CallerPackets.Request config × A → machine.State
  program : Input → OracleComp (FiatShamir.cmaOracleSpec M G F F) (ForgeryHash.forgery config).Value
  implements : machine.ImplementsWithin program fuel
  advance : ∀ q current,
    ∀ next : (FiatShamir.cmaOracleSpec M G F F).Range (CallerHandler.query config q) → machine.State,
      machine.view (stateView (q, current)) = .inr ⟨CallerHandler.query config q, next⟩ →
      ∀ represented answer, SchnorrROM.Caller.replyMatches config q represented answer →
        CallerMachine.Matches machine (CallerHandler.query config) stateView (caller.advance (current, represented)) (next answer)
  initial : ∀ value, CallerMachine.Matches machine (CallerHandler.query config) stateView
    (caller.initial value) (machine.init (inputView value))

def originalFinish (value : Option (ForgeryHash.forgery config).Value × Schnorr.ListROM.Shared.Store F G M) :
    ProbComp (Option ((M × G × F) × F) × Schnorr.ListROM.Shared.Store F G M) :=
  letI := PrivateSampler.Enumerated.sampleable config.sampler
  match value.1 with
  | none => pure (none, value.2)
  | some forge => (fun hashed => (some (forge.val, hashed.1), hashed.2)) <$>
      (Schnorr.ListROM.Shared.interpret
        (Schnorr.ListROM.finalHash (G₂ := G) (K := M) (ForgeryHash.key config forge))).run value.2

theorem terminal_source (packet : Terminal.Input config (P := CallerPackets.Request config × A))
    (valid : Terminal.ready config packet) :
    Terminal.observed config <$> Terminal.source config packet =
      originalFinish config (CallerMachine.observe Subtype.val packet) := by
  rcases packet with ⟨forge | next, saved⟩
  · exact Terminal.source_returned (G₂ := G) (K := M) config forge saved valid
  · exact Terminal.source_cutoff config next saved

variable (ops : Handler.Operations config) (law : Handler.SigningLaw config ops.signing) (fuel : Nat) (witness : Caller.Source config caller fuel)

theorem finish_source_original (value : config.point.Value × config.handler.store.Value)
    (room : SchnorrROM.Caller.admitted config fuel value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    Terminal.observed config <$> finishSource config caller ops fuel value =
      (fun result => (some result.1, result.2)) <$>
        (Schnorr.ListROM.Shared.interpret (Schnorr.ListROM.passWith law.target
          (Subtype.val <$> witness.program (witness.inputView value.1)))).run value.2.val := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have invoked := SchnorrROM.Caller.source_original config (caller.routines config) ops law
    witness.machine witness.stateView witness.inputView witness.advance witness.initial fuel witness.program witness.implements value room
  have finished : Terminal.observed config <$> finishSource config caller ops fuel value =
      (called config caller ops fuel value >>= fun packet =>
        originalFinish config (CallerMachine.observe Subtype.val packet)) := by
    simp only [finishSource, map_bind]
    apply bind_congr_of_forall_mem_support
    intro packet reached
    exact terminal_source config packet (called_ready config caller ops fuel value room packet reached)
  rw [finished, ← bind_map_left]
  change ((CallerMachine.observe Subtype.val <$> SchnorrROM.Caller.source config (caller.routines config) ops fuel value) >>= _) = _
  rw [invoked, bind_map_left]
  simp only [Schnorr.ListROM.passWith, Schnorr.ListROM.Shared.interpret_bind, Schnorr.ListROM.Shared.interpret_simulate,
    simulateQ_map, StateT.run_bind, map_bind, bind_map_left]
  apply bind_congr
  intro answer
  simp only [originalFinish, Schnorr.ListROM.Shared.interpret_pure, map_pure, bind_pure_comp]
  rfl

theorem finish_observe_original (tape : RandomTape w) (value : config.point.Value × config.handler.store.Value)
    (room : SchnorrROM.Caller.admitted config fuel value) (before : State w) (holds : (callerInput config caller).Holds value before) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    (fun result => (Interactive.observe (output config caller) result).map (Terminal.observed config)) <$>
        (finishCode config caller ops fuel).execute (Fresh.port config.handler.sampler.tape) .unit tape before =
      (fun result => some (some result.1, result.2)) <$>
        (Schnorr.ListROM.Shared.interpret (Schnorr.ListROM.passWith law.target
          (Subtype.val <$> witness.program (witness.inputView value.1)))).run value.2.val := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have executed := congrArg (Functor.map (Option.map (Terminal.observed config)))
    ((finish_refines config caller ops fuel).observe tape value room before holds)
  have original := congrArg (Functor.map some) (finish_source_original config caller ops law fuel witness value room)
  simp only [Functor.map_map, Option.map_some] at executed original
  exact executed.trans original

end Signatures.Runtime.CaliperBackend.SchnorrROM.Pass
