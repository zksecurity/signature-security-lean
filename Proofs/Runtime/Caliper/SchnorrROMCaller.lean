import Proofs.Runtime.Caliper.SchnorrROMCallerMemory
import Proofs.Runtime.Caliper.CallerExecution

/-! An adaptive ROM caller built from local initialization and continuation
code. The controller, handler and state-retention copies are generated here.
Every typed request is supported while room for the remaining calls is reserved. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Caller
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A B U : Type} (config : Signing.Enumerated.Configuration w M F G)

def layout (state : Representation w A) (result : Representation w B)
    (fits : 8 * (1 + state.encoding.words + (CallerPackets.request config).encoding.words +
      (CallerPackets.reply config).encoding.words + result.encoding.words + config.handler.store.representation.encoding.words) < 2 ^ w) :
    CallerStep.Layouts w A (CallerPackets.Request config) (CallerPackets.Reply config) B config.handler.store.Value :=
  ⟨state, CallerPackets.request config, CallerPackets.reply config, result, config.handler.store.representation,
    fits, config.sampler.wordFits⟩

/-- Only the caller's local routines are supplied. Each function has an actual
Caliper implementation; no finished controller is an implementation parameter. -/
structure Routines (A B U : Type) where
  state : Representation w A
  result : Representation w B
  fits : 8 * (1 + state.encoding.words + (CallerPackets.request config).encoding.words +
    (CallerPackets.reply config).encoding.words + result.encoding.words + config.handler.store.representation.encoding.words) < 2 ^ w
  advance : A × CallerPackets.Reply config → B ⊕ (CallerPackets.Request config × A)
  continuation : Realizer .unit (CallerStep.resume (layout config state result fits))
    (CallerStep.next (layout config state result fits)) advance
  localNameFits : continuation.savedBuffer < 2 ^ w
  input : Representation w U
  initial : U → B ⊕ (CallerPackets.Request config × A)
  initialization : Realizer .unit input (CallerStep.next (layout config state result fits)) initial
  initialNameFits : initialization.savedBuffer < 2 ^ w
  inputFits : input.encoding.words + config.handler.store.representation.encoding.words < 2 ^ w

variable (routines : Routines config A B U)
def Routines.layout := Caller.layout config routines.state routines.result routines.fits
def Routines.inputLayout := routines.input.prod config.handler.store.representation routines.inputFits
def Routines.outputLayout := CallerStep.output (routines.layout config)

def Invariant (remaining : Nat)
    (value : CallerControl.Frame A (CallerPackets.Request config) config.handler.store.Value) : Prop :=
  Handler.Reserved config remaining value.2.val
def admitted (fuel : Nat) (value : U × config.handler.store.Value) : Prop :=
  Handler.Reserved config fuel value.2.val

theorem initial_invariant (fuel : Nat) (value : U × config.handler.store.Value) (room : admitted config fuel value) :
    CallerControl.Valid (Invariant config) fuel (routines.initial value.1, value.2) := by
  cases head : routines.initial value.1 with
  | inl result => trivial
  | inr pending => exact room

variable [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G] (ops : Handler.Operations config)

def program (fuel : Nat) : Interactive.Code w :=
  CallerControl.program (routines.layout config) (Fresh.port config.handler.sampler.tape)
    routines.advance routines.continuation routines.localNameFits (CallerHandler.code config ops)
    routines.input routines.initial routines.initialization routines.initialNameFits routines.inputFits fuel
def source (fuel : Nat) (value : U × config.handler.store.Value) :
    ProbComp (CallerControl.Packet A (CallerPackets.Request config) B config.handler.store.Value) :=
  CallerControl.start routines.advance (CallerHandler.source config ops) fuel (routines.initial value.1, value.2)

omit [SMul F G] [Sub G] in
theorem available (remaining : Nat) (value) (room : Invariant (A := A) config (remaining + 1) value) :
    CallerPackets.ready config (value.1.1, value.2) :=
  CallerPackets.reserved_ready config remaining (value.1.1, value.2) room

theorem preserves (remaining : Nat) (value) (room : Invariant config (remaining + 1) value)
    (answer) (reached : answer ∈ support (CallerHandler.source config ops (value.1.1, value.2))) :
    CallerControl.Valid (Invariant config) remaining (routines.advance (value.1.2, answer.1), answer.2) := by
  have after := (CallerHandler.reserved_after config ops remaining (value.1.1, value.2) room answer reached).2
  cases head : routines.advance (value.1.2, answer.1) with
  | inl result => trivial
  | inr pending => exact after

theorem refines (fuel : Nat) : Interactive.RefinesOn (admitted config fuel) (Fresh.port config.handler.sampler.tape) .unit
    (routines.inputLayout config) (routines.outputLayout config) (source config routines ops fuel) (program config routines ops fuel) :=
  CallerControl.program_refines (routines.layout config) (Fresh.port config.handler.sampler.tape)
    routines.advance routines.continuation routines.localNameFits (Invariant config) (CallerPackets.ready config)
    (CallerHandler.refines config ops) (available config) (preserves config routines ops)
    routines.input routines.initial routines.initialization routines.initialNameFits routines.inputFits fuel
    (admitted config fuel) (initial_invariant config routines fuel)

end Signatures.Runtime.CaliperBackend.SchnorrROM.Caller
