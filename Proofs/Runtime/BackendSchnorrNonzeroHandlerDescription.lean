import Proofs.Runtime.BackendSchnorrNonzeroHandler
import Proofs.Runtime.BackendSchnorrROMHandlerDescription

/-! Stored-code accounting for nonzero-nonce dispatch and arbitrary callers.
The bound includes both original samplers, their private-tape transformations,
cache code, repair code and every request/reply conversion. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeHandler

open BackendProgram RawTape ListROM ListROM.NativeInterface ListROM.NativeComponents ListROM.NativeHandler

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ K M Input Output : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)
  (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)


include laws dataLaws

def codeDescription : Nat :=
  NativeUniform.descriptionBound rep cost primitive uniform sizes allowance +
    NativeCache.managedDescription rep cost primitive sizes allowance +
    NativeChallenge.descriptionBound rep cost primitive fieldSampler sizes allowance +
    NativeSigning.codeDescription allowance (fun op => sizes.localSize (primitive op))
      (sizes.localSize uniform.request) (sizes.localSize uniform.response)
      (sizes.localSize privatePorts.arity) (sizes.localSize privatePorts.reply)
      (fieldSampler.descriptionSize sizes) (nonzeroSampler.descriptionSize sizes) +
    sizes.localSize (primitive .zero) + sizes.localSize ports.request +
    sizes.localSize ports.randomTag + sizes.localSize ports.hashTag +
    sizes.localSize ports.signingTag + 4096 * allowance + 64

theorem code_description
    (distribute : ∀ {A B T : Type} (a : C.Str A) (b : C.Str B) (t : C.Str T),
      sizes.localSize (QD.distribute a b t) ≤ allowance) :
    (code rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler).descriptionSize sizes ≤
      codeDescription rep bd ports cost primitive uniform privatePorts fieldSampler nonzeroSampler sizes allowance := by
  obtain ⟨hrc, hhc, _, _⟩ := components_description rep data cost primitive uniform privatePorts
    fieldSampler sizes allowance laws dataLaws
  have hsc := NativeComponents.signing_description rep data cost primitive uniform privatePorts
    fieldSampler nonzeroSampler sizes allowance laws dataLaws distribute
  have hr := tagged_description rep bd sizes allowance laws ports.randomTag
    (ListROM.NativeComponents.random rep data cost primitive uniform)
  have hh := tagged_description rep bd sizes allowance laws ports.hashTag
    (ListROM.NativeComponents.hash rep data cost primitive fieldSampler)
  have hs := tagged_description rep bd sizes allowance laws ports.signingTag
    (NativeComponents.signing rep data cost primitive uniform privatePorts fieldSampler nonzeroSampler)
  change (ListROM.NativeHandler.random rep bd ports data cost primitive uniform).descriptionSize sizes ≤ _ at hr
  change (ListROM.NativeHandler.hash rep bd ports data cost primitive fieldSampler).descriptionSize sizes ≤ _ at hh
  have hu := NativeUniform.description rep data cost primitive uniform sizes allowance laws dataLaws
  have hm := NativeCache.managed_description rep data cost primitive (rep.ty NativeUniform.stateTy)
    (NativeDraw.challenge rep data cost primitive fieldSampler) sizes allowance laws dataLaws
  have hd := NativeDraw.challenge_description rep data cost primitive fieldSampler sizes allowance laws dataLaws
  have hi := distribute rep.data.nat (rep.ty hashKey) (rep.ty storeTy)
  have ho := distribute (StepClass.HasSum.sum rep.data.nat (rep.ty hashKey)) (rep.ty message) (rep.ty storeTy)
  dsimp only [code, codeWithSigning, dispatchWithSigning, ListROM.NativeHandler.inner, Code.descriptionSize, codeDescription]
  simp only [positions, NativeInterface.Request, Ty.Value, cryptoBase] at hi ho ⊢
  omega

variable [C.HasOption] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  (dispatchLaws : DispatchDescriptionLaws (Q := Q) sizes allowance)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

include dispatchLaws in
theorem caller_description (fuel : Nat) :
    (caller rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler R fuel).descriptionSize sizes ≤
      sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode +
        codeDescription rep bd ports cost primitive uniform privatePorts fieldSampler nonzeroSampler sizes allowance +
        fuel + 55 * allowance + 26 := by
  have hc := Caller.program_descriptionSize_bound R (rep.ty storeTy) sizes allowance laws dispatchLaws
    (code rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler) fuel
  have hd := code_description rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler
    sizes allowance laws dataLaws dispatchLaws.distribute
  exact hc.trans (by omega)

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeHandler
