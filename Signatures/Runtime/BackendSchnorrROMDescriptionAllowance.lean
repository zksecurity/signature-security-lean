import Signatures.Runtime.BackendSchnorrROMDescriptionInputs

/-! Replace the arbitrary caller's actual stored description by its declared
allowance. Every other description remains the original implementation's size. -/

namespace Signatures.Runtime.Schnorr.ListROM.NativeSolver.DescriptionInputs

def withCaller (d : DescriptionInputs) (limit : Nat) : DescriptionInputs :=
  { d with callerInit := limit, callerHead := 0, callerUpdate := 0 }

theorem solver_withCaller (d : DescriptionInputs) (limit allowance fuel qH : Nat)
    (h : d.callerInit + 2 * d.callerHead + d.callerUpdate ≤ limit) :
    d.solver allowance fuel qH ≤ (d.withCaller limit).solver allowance fuel qH := by
  dsimp only [solver, fork, pass, extraction, handler, privateHandler, uniform,
    challenge, live, managed, signing, withCaller]
  omega

end Signatures.Runtime.Schnorr.ListROM.NativeSolver.DescriptionInputs
