import Proofs.Runtime.BackendSchnorrNonzeroFork
import Proofs.Runtime.BackendSchnorrNonzeroPassDescription
import Proofs.Runtime.BackendSchnorrROMSelectionDescription
import Proofs.Runtime.BackendSchnorrRawForkDescription

/-! Complete stored description of the installed general ROM fork. Both pass
and selector occurrences are bounded from their actual implementations. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeROMFork

open BackendProgram RawTape ListROM ListROM.NativeInterface ListROM.NativeComponents

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [QS : Q.HasSum] [Q.IsDistributive] [Q.HasOption] [OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : ListROM.NativePass.DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (ports : Ports (Q := Q) rep bd)
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
  (dispatchLaws : DispatchDescriptionLaws (Q := Q) sizes allowance)

def codeDescription (fuel qH : Nat) : Nat :=
  2 * NativePass.codeDescription rep bd boundary cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R sizes allowance fuel +
    2 * (2 * sizes.localSize (primitive .scale₁) + sizes.localSize (primitive .add₁) +
      2 * sizes.localSize (primitive .point₁Eq) + sizes.localSize (primitive .messageEq) +
      sizes.localSize (primitive .natAdd) + sizes.localSize (primitive .natLt) + qH + 4096 * allowance + 16) +
    fieldSampler.descriptionSize sizes +
    NativeFork.adapterDescription configTy ListROM.NativePass.outputTy allowance (fun op => sizes.localSize (primitive op)) +
    NativeLookup.descriptionBound rep cost primitive sizes allowance +
    NativeReset.descriptionBound rep cost primitive sizes allowance +
    3 * sizes.localSize (QS.inl rep.data.unit (rep.ty (.pair ListROM.NativePass.outputTy ListROM.NativePass.outputTy))) +
    sizes.localSize (QS.inr rep.data.unit (rep.ty (.pair ListROM.NativePass.outputTy ListROM.NativePass.outputTy))) +
    128 * allowance + 128

include laws dataLaws dispatchLaws

theorem code_description (fuel qH : Nat) :
    (code rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R fuel qH).descriptionSize sizes ≤
      codeDescription rep bd boundary cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R sizes allowance fuel qH := by
  have hp := NativePass.code_description rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R
    sizes allowance laws dataLaws dispatchLaws fuel
  have hs := NativeSelection.selector_description rep data cost primitive qH sizes allowance laws dataLaws
  have hf := NativeFork.description rep data cost primitive (NativeSelection.selector rep data cost primitive qH)
    (NativePass.code rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R fuel) fieldSampler
    sizes allowance laws dataLaws
  change (NativeFork.code rep data cost primitive (NativeSelection.selector rep data cost primitive qH)
    (NativePass.code rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R fuel) fieldSampler).descriptionSize sizes ≤ _
  unfold NativeFork.descriptionBound at hf
  unfold codeDescription
  dsimp only at *
  omega

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeROMFork
