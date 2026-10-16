import Signatures.Runtime.BackendSchnorrNonzeroDescriptionInputs
import Signatures.Runtime.BackendSchnorrROMDescriptionAllowance

/-! Replace the actual attacker's stored description by its declared allowance.
Both sampler descriptions and all primitive/port descriptions remain explicit. -/

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeSolver.DescriptionInputs

def withCaller (d : DescriptionInputs) (limit : Nat) : DescriptionInputs :=
  { d with common := d.common.withCaller limit }

theorem solver_withCaller (d : DescriptionInputs) (limit allowance fuel qH : Nat)
    (h : d.common.callerInit + 2 * d.common.callerHead + d.common.callerUpdate ≤ limit) :
    d.solver allowance fuel qH ≤ (d.withCaller limit).solver allowance fuel qH := by
  dsimp only [solver, fork, pass, handler, withCaller,
    ListROM.NativeSolver.DescriptionInputs.withCaller, ListROM.NativeSolver.DescriptionInputs.uniform,
    ListROM.NativeSolver.DescriptionInputs.challenge, ListROM.NativeSolver.DescriptionInputs.live,
    ListROM.NativeSolver.DescriptionInputs.managed, ListROM.NativeSolver.DescriptionInputs.extraction]
  omega

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeSolver.DescriptionInputs
