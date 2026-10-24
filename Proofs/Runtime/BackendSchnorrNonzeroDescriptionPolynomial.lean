import Proofs.Runtime.BackendSchnorrNonzeroDescriptionInputs
import Proofs.Runtime.BackendSchnorrROMDescriptionPolynomial

/-! Polynomial stored code for the actual complete nonzero-nonce solver, from
both original sampler descriptions and the shared original component inputs. -/

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeSolver.DescriptionInputs

open BackendProgram RawTape ListROM

structure Polynomial (d : Nat → DescriptionInputs) : Prop where
  common : ListROM.NativeSolver.DescriptionInputs.Polynomial (fun n => (d n).common)
  nonzeroSamplerSize : PolynomiallyBounded (fun n => (d n).nonzeroSamplerSize)

private def signingSize (d : DescriptionInputs) (allowance : Nat) : Nat :=
  NativeSigning.codeDescription allowance d.common.primitiveSize d.common.uniformRequest d.common.uniformResponse
    d.common.privateArity d.common.privateReply d.common.samplerSize d.nonzeroSamplerSize

private theorem handler_le_common (d : DescriptionInputs) (allowance : Nat) :
    d.handler allowance ≤ d.common.handler allowance + signingSize d allowance := by
  dsimp only [handler, ListROM.NativeSolver.DescriptionInputs.handler, signingSize]
  omega

private theorem pass_le_common (d : DescriptionInputs) (allowance fuel : Nat) :
    d.pass allowance fuel ≤ d.common.pass allowance fuel + signingSize d allowance := by
  have h := handler_le_common d allowance
  dsimp only [pass, ListROM.NativeSolver.DescriptionInputs.pass]
  omega

/-- A numerical envelope reuses the shared description polynomial and adds the
actual nonzero signer twice. It supplies no semantic or efficiency assumption. -/
theorem solver_le_common (d : DescriptionInputs) (allowance fuel qH : Nat) :
    d.solver allowance fuel qH ≤ d.common.solver allowance fuel qH + 2 *
      NativeSigning.codeDescription allowance d.common.primitiveSize d.common.uniformRequest d.common.uniformResponse
        d.common.privateArity d.common.privateReply d.common.samplerSize d.nonzeroSamplerSize := by
  have h := pass_le_common d allowance fuel
  dsimp only [solver, fork, ListROM.NativeSolver.DescriptionInputs.solver,
    ListROM.NativeSolver.DescriptionInputs.fork]
  change _ ≤ _ + 2 * signingSize d allowance
  omega

theorem solver_polynomial (d : Nat → DescriptionInputs) (allowance fuel qH : Nat → Nat)
    (h : Polynomial d) (hAllowance : PolynomiallyBounded allowance)
    (hFuel : PolynomiallyBounded fuel) (hQueries : PolynomiallyBounded qH) :
    PolynomiallyBounded (fun n => (d n).solver (allowance n) (fuel n) (qH n)) := by
  have hsign := NativeSigning.codeDescription_polynomial allowance (fun n => (d n).common.primitiveSize)
    (fun n => (d n).common.uniformRequest) (fun n => (d n).common.uniformResponse)
    (fun n => (d n).common.privateArity) (fun n => (d n).common.privateReply)
    (fun n => (d n).common.samplerSize) (fun n => (d n).nonzeroSamplerSize)
    hAllowance h.common.primitive h.common.uniformRequest h.common.uniformResponse
    h.common.privateArity h.common.privateReply h.common.samplerSize h.nonzeroSamplerSize
  have hcommon := ListROM.NativeSolver.DescriptionInputs.solver_polynomial (fun n => (d n).common)
    allowance fuel qH h.common hAllowance hFuel hQueries
  exact (hcommon.add ((PolynomiallyBounded.const 2).mul hsign)).of_le
    (fun n => solver_le_common (d n) (allowance n) (fuel n) (qH n))

theorem compiled_polynomial (d : Nat → DescriptionInputs) (factor allowance fuel qH : Nat → Nat)
    (h : Polynomial d) (hFactor : PolynomiallyBounded factor) (hAllowance : PolynomiallyBounded allowance)
    (hFuel : PolynomiallyBounded fuel) (hQueries : PolynomiallyBounded qH) :
    PolynomiallyBounded (fun n => factor n * (d n).solver (allowance n) (fuel n) (qH n)) :=
  hFactor.mul (solver_polynomial d allowance fuel qH h hAllowance hFuel hQueries)

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeSolver.DescriptionInputs
