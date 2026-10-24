import Proofs.Runtime.Caliper.SchnorrROMCallerPostcondition

/-! The generated adaptive caller executes the original OracleMachine and its
ROM oracle. Only local caller-step correspondence is assumed; equivalence of the
complete controller is derived. The original implementation excludes fuel cutoff. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Caller
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A B U : Type} (config : Signing.Enumerated.Configuration w M F G)

def replyMatches (request : CallerPackets.Request config) (represented : CallerPackets.Reply config)
    (original : (FiatShamir.cmaOracleSpec M G F F).Range (CallerHandler.query config request)) : Prop :=
  CallerHandler.replyValue config represented = CallerHandler.representReply config request original

variable {V : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
    [DecidableEq M] [DecidableEq G]

/-- The original oracle of a list-backend handler on the shared store. -/
def original (target : Schnorr.ListROM.Handler F G G M M) :
    QueryImpl (FiatShamir.cmaOracleSpec M G F F) (StateT (Schnorr.ListROM.Shared.Store F G M) ProbComp) :=
  letI := PrivateSampler.Enumerated.sampleable config.sampler
  fun query => Schnorr.ListROM.Shared.interpret (target query)

variable (routines : Routines config A B U) (ops : Handler.Operations config) (law : Handler.SigningLaw config ops.signing)
    (machine : OracleMachine (FiatShamir.cmaOracleSpec M G F F) V B)
    (stateView : CallerPackets.Request config × A → machine.State) (inputView : U → V)
    (advanceMatches : ∀ query current,
      ∀ next : (FiatShamir.cmaOracleSpec M G F F).Range (CallerHandler.query config query) → machine.State,
        machine.view (stateView (query, current)) = .inr ⟨CallerHandler.query config query, next⟩ →
        ∀ represented answer, replyMatches config query represented answer →
          CallerMachine.Matches machine (CallerHandler.query config) stateView (routines.advance (current, represented)) (next answer))
    (initialMatches : ∀ value, CallerMachine.Matches machine (CallerHandler.query config) stateView
      (routines.initial value) (machine.init (inputView value)))

include advanceMatches initialMatches in
theorem source_original (fuel : Nat) (sourceProgram : V → OracleComp (FiatShamir.cmaOracleSpec M G F F) B)
    (implements : machine.ImplementsWithin sourceProgram fuel)
    (value : U × config.handler.store.Value) (room : admitted config fuel value) :
    CallerMachine.observe Subtype.val <$> source config routines ops fuel value =
      (fun answer => (some answer.1, answer.2)) <$>
        (simulateQ (original config law.target) (sourceProgram (inputView value.1))).run value.2.val := by
  apply CallerMachine.start_eq_simulateQ machine (CallerHandler.query config) stateView Subtype.val (replyMatches config)
    routines.advance (CallerHandler.source config ops) (original config law.target) (Invariant config) _ _
    (preserves config routines ops) fuel (routines.initial value.1, value.2) (inputView value.1)
    (initial_invariant config routines fuel value room) (initialMatches value.1) sourceProgram implements
  · intro remaining packet valid
    exact CallerHandler.synchronizes config ops law (packet.1.1, packet.2) (available config remaining packet valid)
  · intro remaining query current saved valid
    exact advanceMatches query current

include advanceMatches initialMatches in
theorem observe_source (fuel : Nat) (sourceProgram : V → OracleComp (FiatShamir.cmaOracleSpec M G F F) B)
    (implements : machine.ImplementsWithin sourceProgram fuel)
    (tape : RandomTape w) (value : U × config.handler.store.Value) (room : admitted config fuel value)
    (before : State w) (holds : (routines.inputLayout config).Holds value before) :
    (fun finished => CallerMachine.observe Subtype.val <$> Interactive.observe (routines.outputLayout config) finished) <$>
        (program config routines ops fuel).execute (Fresh.port config.handler.sampler.tape) .unit tape before =
      (fun answer => some (some answer.1, answer.2)) <$>
        (simulateQ (original config law.target) (sourceProgram (inputView value.1))).run value.2.val := by
  apply CallerMachine.program_observe_source machine (CallerHandler.query config) stateView Subtype.val (replyMatches config)
    routines.advance (CallerHandler.source config ops) (original config law.target) (Invariant config) _ _
    (preserves config routines ops) (routines.layout config) (Fresh.port config.handler.sampler.tape)
    routines.continuation routines.localNameFits (CallerHandler.code config ops) (CallerPackets.ready config)
    (CallerHandler.refines config ops) (available config)
    routines.input routines.initial routines.initialization routines.initialNameFits routines.inputFits fuel
    (admitted config fuel) (initial_invariant config routines fuel) inputView (fun value _ => initialMatches value.1)
    sourceProgram implements tape value room before holds
  · intro remaining packet valid
    exact CallerHandler.synchronizes config ops law (packet.1.1, packet.2) (available config remaining packet valid)
  · intro remaining query current saved valid
    exact advanceMatches query current

end Signatures.Runtime.CaliperBackend.SchnorrROM.Caller
