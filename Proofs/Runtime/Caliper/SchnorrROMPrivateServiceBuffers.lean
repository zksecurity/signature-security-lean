import Proofs.Runtime.Caliper.SchnorrROMPrivateServiceBounds
import Proofs.Runtime.Caliper.CallerBuffers

/-! The complete private sampler uses a fixed scratch-buffer extent. Retaining
a scalar across another call needs headroom above local caller code, independent
of the number of internal uniform queries and the generated program length. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler
open Caliper BoundedSource
variable {w : Nat} {F C : Type} (layout : Layouts w F C)

theorem Finish.buffers (zero : layout.tape.scalar.Value) : (Finish.program layout zero).code.memBound ≤ 3 := by
  have distributed := CallerControl.distribute_buffers (step layout)
  have constant := Finish.constant_buffers layout zero
  have retained := (Finish.constant layout zero).retain_buffers (by decide) (Read.tapes layout.tape).representation
    layout.tape.wordFits (Finish.constant_nameFits layout zero) (CallerStep.frame (step layout)).fits
    (CallerControl.result (step layout)).fits
  change (Finish.fallback layout zero).code.memBound ≤ _ at retained
  change max (CallerControl.distribute (step layout)).code.memBound (Dispatch.code .skip _ _ _).memBound ≤ 3
  refine max_le distributed ((Dispatch.buffers _ _ _ _).trans ?_)
  change max 2 (max 0 (Finish.fallback layout zero).code.memBound) ≤ 3
  omega

namespace Service
variable [Zero F] (caller : Caller layout) (zeroValid : layout.tape.scalar.valid 0)

def bufferBudget := max 8 (max caller.continuation.code.memBound caller.initialCode.code.memBound) + 1

theorem buffers (fuel : Nat) :
    ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).memBound ≤ bufferBudget layout caller := by
  have generated := CallerControl.program_buffers (step layout) (Fresh.port layout.tape)
    caller.advance caller.continuation caller.localFits (PrivateQuery.code layout.tape zeroValid)
    layout.tape.unit.representation caller.initial caller.initialCode caller.initialFits (inputFits layout) fuel
  have handled := PrivateQuery.buffers layout.tape zeroValid
  have finished := Finish.buffers layout ⟨0, zeroValid⟩
  change ((PrivateSampler.code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).memBound ≤ _ at generated
  change max ((PrivateSampler.code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).memBound
    (Finish.program layout ⟨0, zeroValid⟩).code.memBound ≤ _
  unfold bufferBudget
  omega

theorem savedBuffer_fits (fuel : Nat)
    (localHeadroom : caller.continuation.code.memBound + 1 < 2 ^ w)
    (initialHeadroom : caller.initialCode.code.memBound + 1 < 2 ^ w) :
    Interactive.savedBuffer (Fresh.port layout.tape) (code layout caller zeroValid fuel) < 2 ^ w := by
  have bounded := buffers layout caller zeroValid fuel
  have := layout.tape.wordFits
  unfold Interactive.savedBuffer
  unfold bufferBudget at bounded
  omega

end Service
end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler
