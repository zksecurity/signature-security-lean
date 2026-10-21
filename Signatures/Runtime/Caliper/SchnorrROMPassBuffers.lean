import Signatures.Runtime.Caliper.SchnorrROMPassBounds
import Signatures.Runtime.Caliper.CallerBuffers

/-! The complete pass's scratch extent is derived from its local callers and
cryptographic routines. Reserving an outer saved buffer needs one extra name
beyond the inner retained calls, independently of the pass fuel. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Pass
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G A : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Caller config A) (ops : Handler.Operations config)

def bufferBudget := max 13 (max (ops.slots + 4)
  (max (caller.continuation.code.memBound + 1) (caller.initialization.code.memBound + 1)))
theorem buffers (fuel : Nat) : ((program config caller ops fuel).lower (Fresh.port config.handler.sampler.tape)).memBound ≤
    bufferBudget config caller ops := by
  have controlled := CallerControl.program_buffers ((caller.routines config).layout config)
    (Fresh.port config.handler.sampler.tape) caller.advance caller.continuation caller.localNameFits
    (CallerHandler.code config ops) config.point.representation caller.initial caller.initialization
    caller.initialNameFits (inputFits config) fuel
  have serviced := CallerHandler.buffers config ops
  have finished := Terminal.buffers config (caller.pending config) (caller.terminalRoom config)
  have initialized := Initialization.buffers config
  change ((SchnorrROM.Caller.program config (caller.routines config) ops fuel).lower _).memBound ≤ _ at controlled
  change max (Initialization.code config).code.memBound
    (max ((SchnorrROM.Caller.program config (caller.routines config) ops fuel).lower _).memBound
      ((Terminal.code config (caller.pending config) (caller.terminalRoom config)).lower _).memBound) ≤ _
  unfold bufferBudget
  omega

def replayNameRoom : Prop := ops.slots + 4 < 2 ^ w ∧
  caller.continuation.code.memBound + 1 < 2 ^ w ∧ caller.initialization.code.memBound + 1 < 2 ^ w
theorem savedNameFits (room : replayNameRoom config caller ops) (fuel : Nat) :
    Interactive.savedBuffer (Fresh.port config.handler.sampler.tape) (program config caller ops fuel) < 2 ^ w := by
  have bounded := buffers config caller ops fuel
  have width := config.sampler.wordFits
  unfold bufferBudget at bounded
  unfold Interactive.savedBuffer
  rcases room with ⟨primitives, localCode, initialCode⟩
  omega

end Signatures.Runtime.CaliperBackend.SchnorrROM.Pass
