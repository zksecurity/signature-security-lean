import Proofs.Runtime.BackendSchnorrROMSolverDescription

/-! Numerical descriptions of the original caller, sampler, primitives and
interface adapters. The formula equals the complete native solver's existing
stored-code bound; it is independent of the curve and message types. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativeSolver

open BackendProgram RawTape NativeInterface NativeComponents

structure DescriptionInputs where
  primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat
  samplerSize : Nat
  callerInit : Nat
  callerHead : Nat
  callerUpdate : Nat
  inputPort : Nat
  outputPort : Nat
  optionalPort : Nat
  requestPort : Nat
  randomTag : Nat
  hashTag : Nat
  signingTag : Nat
  uniformRequest : Nat
  uniformResponse : Nat
  privateArity : Nat
  privateReply : Nat
  rejectSize : Nat
  acceptSize : Nat

namespace DescriptionInputs

def uniform (d : DescriptionInputs) (allowance : Nat) : Nat :=
  Expression.descriptionBound allowance d.primitiveSize NativeUniform.prepareExpression +
  Expression.descriptionBound allowance d.primitiveSize NativeUniform.hitExpression +
  Expression.descriptionBound allowance d.primitiveSize NativeUniform.saveExpression +
  d.uniformRequest + d.uniformResponse + 14 * allowance + 12

def challenge (d : DescriptionInputs) (allowance : Nat) : Nat :=
  Expression.descriptionBound allowance d.primitiveSize NativeChallenge.prepareExpression +
  Expression.descriptionBound allowance d.primitiveSize NativeChallenge.saveExpression +
  d.samplerSize + 14 * allowance + 9

def live (d : DescriptionInputs) (allowance : Nat) : Nat :=
  Language.descriptionBound allowance d.primitiveSize (fun _ => 0)
    (cacheGetExpr (Cmd := SampledCache.Draw scalar) hashEq .sample)

def managed (d : DescriptionInputs) (allowance : Nat) : Nat :=
  Language.descriptionBound allowance d.primitiveSize (fun _ => 0)
    (managedGet (Cmd := SampledCache.Draw scalar) .sample)

def signing (d : DescriptionInputs) (allowance : Nat) : Nat :=
  Language.descriptionBound allowance d.primitiveSize (fun _ => 0)
    (signCached (Cmd := SampledCache.Draw scalar) .sample)

def privateHandler (d : DescriptionInputs) (allowance : Nat) : Nat :=
  d.uniform allowance + d.privateArity + d.privateReply + 14 * allowance + 11

def handler (d : DescriptionInputs) (allowance : Nat) : Nat :=
  d.uniform allowance + d.managed allowance + d.signing allowance +
    (d.challenge allowance + allowance + 2) +
    2 * ((d.privateHandler allowance + 18 * allowance + 6) * d.samplerSize) +
    d.primitiveSize .zero + d.requestPort + d.randomTag + d.hashTag + d.signingTag +
    4096 * allowance + 64

def pass (d : DescriptionInputs) (allowance fuel : Nat) : Nat :=
  d.callerInit + 2 * d.callerHead + d.callerUpdate + d.handler allowance +
    d.challenge allowance + d.live allowance + d.primitiveSize .zero +
    d.inputPort + d.outputPort + d.optionalPort + fuel + 8192 * allowance + 128

def fork (d : DescriptionInputs) (allowance fuel qH : Nat) : Nat :=
  2 * d.pass allowance fuel +
    2 * (2 * d.primitiveSize .scale₁ + d.primitiveSize .add₁ +
      2 * d.primitiveSize .point₁Eq + d.primitiveSize .messageEq +
      d.primitiveSize .natAdd + d.primitiveSize .natLt + qH + 4096 * allowance + 16) +
    d.samplerSize + NativeFork.adapterDescription configTy NativePass.outputTy allowance d.primitiveSize +
    (Expression.descriptionBound allowance d.primitiveSize NativeLookup.expression + 4 * allowance + 1) +
    (Expression.descriptionBound allowance d.primitiveSize NativeReset.expression + 4 * allowance + 1) +
    3 * d.rejectSize + d.acceptSize + 128 * allowance + 128

def extraction (d : DescriptionInputs) (allowance : Nat) : Nat :=
  2 * d.samplerSize + 2 * d.primitiveSize .sub + d.primitiveSize .div +
    d.primitiveSize .point₁Eq + d.primitiveSize .scalarEq + 3 * d.primitiveSize .zero + 8192 * allowance + 32

def solver (d : DescriptionInputs) (allowance fuel qH : Nat) : Nat :=
  d.fork allowance fuel qH + d.extraction allowance + 64 * allowance + 4

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
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (sizes : DescriptionSize Q)
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : NativePass.DataPorts (Q := Q) rep bd)
  (ports : Ports (Q := Q) rep bd)
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

def descriptionInputs : DescriptionInputs where
  primitiveSize op := sizes.localSize (primitive op)
  samplerSize := sampler.descriptionSize sizes
  callerInit := sizes.localSize R.initCode
  callerHead := sizes.localSize R.headCode
  callerUpdate := sizes.localSize R.updateCode
  inputPort := sizes.localSize boundary.input
  outputPort := sizes.localSize boundary.output
  optionalPort := sizes.localSize boundary.optional
  requestPort := sizes.localSize ports.request
  randomTag := sizes.localSize ports.randomTag
  hashTag := sizes.localSize ports.hashTag
  signingTag := sizes.localSize ports.signingTag
  uniformRequest := sizes.localSize uniform.request
  uniformResponse := sizes.localSize uniform.response
  privateArity := sizes.localSize privatePorts.arity
  privateReply := sizes.localSize privatePorts.reply
  rejectSize := sizes.localSize (QS.inl rep.data.unit (rep.ty (.pair NativePass.outputTy NativePass.outputTy)))
  acceptSize := sizes.localSize (QS.inr rep.data.unit (rep.ty (.pair NativePass.outputTy NativePass.outputTy)))

omit [Q.HasCategory] [Q.HasProd] [Q.IsDistributive] [Q.HasOption] [OptionCode (Q := Q)] in
theorem codeDescription_eq (allowance fuel qH : Nat) :
    codeDescription rep cost primitive sampler sizes allowance bd boundary ports uniform privatePorts R fuel qH =
      (descriptionInputs rep cost primitive sampler sizes bd boundary ports uniform privatePorts R).solver allowance fuel qH := rfl

end Signatures.Runtime.Schnorr.ListROM.NativeSolver
