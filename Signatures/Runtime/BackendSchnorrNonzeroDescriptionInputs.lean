import Signatures.Runtime.BackendSchnorrNonzeroSolverDescription
import Signatures.Runtime.BackendSchnorrROMDescriptionInputs

/-! Numerical stored-code inputs for the complete nonzero-nonce solver.
Shared caller/primitive/port measurements are reused; the distinct nonzero
sampler description is an additional original input. No solver size is assumed. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeSolver

open BackendProgram RawTape ListROM ListROM.NativeInterface ListROM.NativeComponents

structure DescriptionInputs where
  common : ListROM.NativeSolver.DescriptionInputs
  nonzeroSamplerSize : Nat

namespace DescriptionInputs

def handler (d : DescriptionInputs) (allowance : Nat) : Nat :=
  d.common.uniform allowance + d.common.managed allowance + d.common.challenge allowance +
    NativeSigning.codeDescription allowance d.common.primitiveSize d.common.uniformRequest d.common.uniformResponse
      d.common.privateArity d.common.privateReply d.common.samplerSize d.nonzeroSamplerSize +
    d.common.primitiveSize .zero + d.common.requestPort + d.common.randomTag + d.common.hashTag + d.common.signingTag +
    4096 * allowance + 64

def pass (d : DescriptionInputs) (allowance fuel : Nat) : Nat :=
  d.common.callerInit + 2 * d.common.callerHead + d.common.callerUpdate + d.handler allowance +
    d.common.challenge allowance + d.common.live allowance + d.common.primitiveSize .zero +
    d.common.inputPort + d.common.outputPort + d.common.optionalPort + fuel + 8192 * allowance + 128

def fork (d : DescriptionInputs) (allowance fuel qH : Nat) : Nat :=
  2 * d.pass allowance fuel +
    2 * (2 * d.common.primitiveSize .scale₁ + d.common.primitiveSize .add₁ +
      2 * d.common.primitiveSize .point₁Eq + d.common.primitiveSize .messageEq +
      d.common.primitiveSize .natAdd + d.common.primitiveSize .natLt + qH + 4096 * allowance + 16) +
    d.common.samplerSize + NativeFork.adapterDescription configTy ListROM.NativePass.outputTy allowance d.common.primitiveSize +
    (Expression.descriptionBound allowance d.common.primitiveSize NativeLookup.expression + 4 * allowance + 1) +
    (Expression.descriptionBound allowance d.common.primitiveSize NativeReset.expression + 4 * allowance + 1) +
    3 * d.common.rejectSize + d.common.acceptSize + 128 * allowance + 128

def solver (d : DescriptionInputs) (allowance fuel qH : Nat) : Nat :=
  d.fork allowance fuel qH + d.common.extraction allowance + 64 * allowance + 4

end DescriptionInputs

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [QS : Q.HasSum] [Q.IsDistributive] [Q.HasOption] [OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (sizes : DescriptionSize Q)
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : ListROM.NativePass.DataPorts (Q := Q) rep bd)
  (ports : Ports (Q := Q) rep bd)
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

def descriptionInputs : DescriptionInputs where
  common := ListROM.NativeSolver.descriptionInputs rep cost primitive fieldSampler sizes bd boundary ports uniform privatePorts R
  nonzeroSamplerSize := nonzeroSampler.descriptionSize sizes

omit [Q.HasCategory] [Q.HasProd] [Q.IsDistributive] [Q.HasOption] [OptionCode (Q := Q)] in
theorem codeDescription_eq (allowance fuel qH : Nat) :
    codeDescription rep cost primitive fieldSampler nonzeroSampler sizes allowance bd boundary ports uniform privatePorts R fuel qH =
      (descriptionInputs rep cost primitive fieldSampler nonzeroSampler sizes bd boundary ports uniform privatePorts R).solver allowance fuel qH := rfl

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeSolver
