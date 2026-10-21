import Signatures.Runtime.Caliper.SchnorrROMTerminalSource

/-! One caller followed by final verification hashing. The pass fixes the public
key and forgery encodings; only the attacker's local state and local code are
supplied. Final-hash admission follows from the generated caller's exit theorem. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Pass
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} (config : Signing.Enumerated.Configuration w M F G)

def control (state : Representation w A)
    (fits : 8 * (1 + state.encoding.words + (CallerPackets.request config).encoding.words +
      (CallerPackets.reply config).encoding.words + (ForgeryHash.forgery config).representation.encoding.words +
      config.handler.store.representation.encoding.words) < 2 ^ w) :=
  Caller.layout config state (ForgeryHash.forgery config).representation fits

structure Caller (A : Type) where
  state : Representation w A
  fits : 8 * (1 + state.encoding.words + (CallerPackets.request config).encoding.words +
    (CallerPackets.reply config).encoding.words + (ForgeryHash.forgery config).representation.encoding.words +
    config.handler.store.representation.encoding.words) < 2 ^ w
  advance : A × CallerPackets.Reply config → (ForgeryHash.forgery config).Value ⊕ (CallerPackets.Request config × A)
  continuation : Realizer .unit (CallerStep.resume (control config state fits)) (CallerStep.next (control config state fits)) advance
  localNameFits : continuation.savedBuffer < 2 ^ w
  initial : config.point.Value → (ForgeryHash.forgery config).Value ⊕ (CallerPackets.Request config × A)
  initialization : Realizer .unit config.point.representation (CallerStep.next (control config state fits)) initial
  initialNameFits : initialization.savedBuffer < 2 ^ w

theorem inputFits : config.point.representation.encoding.words + config.handler.store.representation.encoding.words < 2 ^ w := by
  have key := FinalHash.key_le config
  have saved := FinalHash.store_le config
  change config.message.representation.encoding.words + config.point.representation.encoding.words ≤ _ at key
  exact config.handler.fits_of_le (by omega)

variable (caller : Caller config A)
def Caller.routines : SchnorrROM.Caller.Routines config A (ForgeryHash.forgery config).Value config.point.Value where
  state := caller.state
  result := (ForgeryHash.forgery config).representation
  fits := caller.fits
  advance := caller.advance
  continuation := caller.continuation
  localNameFits := caller.localNameFits
  input := config.point.representation
  initial := caller.initial
  initialization := caller.initialization
  initialNameFits := caller.initialNameFits
  inputFits := inputFits config

def Caller.pending := CallerStep.pending ((caller.routines config).layout config)
theorem Caller.terminalRoom : 8 * Terminal.width config (caller.pending config) < 2 ^ w := by
  have room := caller.fits
  change 8 * (1 + _ + ((CallerPackets.request config).encoding.words + caller.state.encoding.words) + _) < _
  omega
def callerInput := (caller.routines config).inputLayout config
def output := Terminal.output config (caller.pending config) (caller.terminalRoom config)

variable [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G] (ops : Handler.Operations config)
def called (fuel : Nat) := SchnorrROM.Caller.source config (caller.routines config) ops fuel
def finishSource (fuel : Nat) (value : config.point.Value × config.handler.store.Value) : ProbComp (Terminal.Output config) :=
  called config caller ops fuel value >>= Terminal.source config
def finishCode (fuel : Nat) : Interactive.Code w :=
  .seq (SchnorrROM.Caller.program config (caller.routines config) ops fuel)
    (Terminal.code config (caller.pending config) (caller.terminalRoom config))

theorem called_ready (fuel : Nat) (value : config.point.Value × config.handler.store.Value)
    (room : SchnorrROM.Caller.admitted config fuel value) (answer)
    (reached : answer ∈ support (called config caller ops fuel value)) : Terminal.ready config answer :=
  Terminal.reserved_ready config answer
    (SchnorrROM.Caller.start_postcondition config (caller.routines config) ops fuel
      (caller.initial value.1, value.2) room answer reached).reserved

theorem finish_refines (fuel : Nat) : Interactive.RefinesOn (SchnorrROM.Caller.admitted config fuel)
    (Fresh.port config.handler.sampler.tape) .unit (callerInput config caller) (output config caller)
    (finishSource config caller ops fuel) (finishCode config caller ops fuel) :=
  (SchnorrROM.Caller.refines config (caller.routines config) ops fuel).seq
    (Terminal.refines config (caller.pending config) (caller.terminalRoom config)) (called_ready config caller ops fuel)

theorem finish_preserves_config (fuel : Nat) (value : config.point.Value × config.handler.store.Value)
    (room : SchnorrROM.Caller.admitted config fuel value) (answer)
    (reached : answer ∈ support (finishSource config caller ops fuel value)) : answer.2.val.1.1 = value.2.val.1.1 := by
  simp only [finishSource, support_bind, Set.mem_iUnion] at reached
  obtain ⟨packet, supported, finished⟩ := reached
  exact (Terminal.preserves_config config packet answer finished).trans
    (SchnorrROM.Caller.start_postcondition config (caller.routines config) ops fuel
      (caller.initial value.1, value.2) room packet supported).config

end Signatures.Runtime.CaliperBackend.SchnorrROM.Pass
