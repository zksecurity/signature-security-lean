import Proofs.Runtime.BackendSchnorrNonzeroPass
import Proofs.Runtime.BackendSchnorrNonzeroHandlerDescription
import Proofs.Runtime.BackendSchnorrROMPassDescription

/-! Stored-code accounting for the complete nonzero-nonce native pass, including
both samplers, attacker code, conversions, cutoff and final live-cache hashing. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativePass

open BackendProgram RawTape ListROM ListROM.NativeInterface ListROM.NativeComponents ListROM.NativePass

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [QD : Q.IsDistributive] [Q.HasOption] [OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (ports : Ports (Q := Q) rep bd)
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

  (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
  (dispatchLaws : DispatchDescriptionLaws (Q := Q) sizes allowance)

include laws dataLaws dispatchLaws

def codeDescription (fuel : Nat) : Nat :=
  sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode +
    NativeHandler.codeDescription rep bd ports cost primitive uniform privatePorts fieldSampler nonzeroSampler sizes allowance +
    NativeChallenge.descriptionBound rep cost primitive fieldSampler sizes allowance +
    NativeCache.liveDescription rep cost primitive sizes allowance + sizes.localSize (primitive .zero) +
    sizes.localSize boundary.input + sizes.localSize boundary.output + sizes.localSize boundary.optional +
    fuel + 8192 * allowance + 128

theorem code_description (fuel : Nat) :
    (code rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R fuel).descriptionSize sizes ≤
      codeDescription rep bd boundary cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R sizes allowance fuel := by
  have hs := setup_description (iface := iface) rep bd boundary data cost primitive sizes allowance laws dataLaws
  have ht := terminal_description rep bd boundary data cost primitive fieldSampler sizes allowance laws dataLaws dispatchLaws
  have hc := NativeHandler.caller_description rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler
    sizes allowance laws dataLaws dispatchLaws R fuel
  have hf := ListROM.NativeHandler.finalHash_description rep data cost primitive fieldSampler sizes allowance laws dataLaws
  dsimp only [code, Code.descriptionSize, codeDescription]
  omega

end Signatures.Runtime.Schnorr.NonzeroListROM.NativePass
