import Proofs.Runtime.BackendSchnorrROMPass

/-! Stored code for the complete native pass. Every boundary adapter, cutoff
branch, final-live-hash routine and occurrence of the original/transformed
sampler is counted, together with the arbitrary caller's stored description. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativePass

open BackendProgram RawTape NativeInterface NativeComponents

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
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (ports : Ports (Q := Q) rep bd)
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

  (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
  (dispatchLaws : DispatchDescriptionLaws (Q := Q) sizes allowance)

include laws dataLaws

omit QD [Q.HasOption] [OptionCode (Q := Q)] in
theorem setup_description :
    (setup (iface := iface) rep bd boundary data cost primitive).descriptionSize sizes ≤
      sizes.localSize boundary.input + 1024 * allowance + 4 := by
  have h := localCode_description rep data cost primitive initialExpression sizes allowance laws dataLaws
  have he : sizes.localSize (localCode rep data cost primitive initialExpression) ≤ 1024 * allowance :=
    h.trans (by simp only [initialExpression, Expression.descriptionBound, Expression.variableDescription]; omega)
  dsimp only [setup, Code.descriptionSize]
  omega

omit [C.HasOption] QD [Q.HasOption] [OptionCode (Q := Q)] in
theorem verify_description :
    (verify rep data cost primitive sampler).descriptionSize sizes ≤
      (NativeComponents.finalHash rep data cost primitive sampler).descriptionSize sizes + 2048 * allowance + 8 := by
  refine (wrap_description rep data cost primitive forgery verifyInput verifyOutput
    (NativeComponents.finalHash rep data cost primitive sampler) sizes allowance laws dataLaws).trans ?_
  simp only [verifyInput, verifyOutput, Expression.descriptionBound, Expression.variableDescription]
  omega

omit QD [Q.HasOption] [OptionCode (Q := Q)] in
theorem finishSome_description :
    (finishSome rep bd boundary data cost primitive sampler).descriptionSize sizes ≤
      (NativeComponents.finalHash rep data cost primitive sampler).descriptionSize sizes +
        sizes.localSize boundary.output + 3072 * allowance + 16 := by
  have hv := verify_description rep data cost primitive sampler sizes allowance laws dataLaws
  have h := localCode_description rep data cost primitive singletonExpression sizes allowance laws dataLaws
  have he : sizes.localSize (localCode rep data cost primitive singletonExpression) ≤ 1024 * allowance :=
    h.trans (by simp only [singletonExpression, Expression.descriptionBound, Expression.variableDescription]; omega)
  dsimp only [finishSome, Code.descriptionSize]
  omega

omit [C.HasOption] QD [Q.HasOption] [OptionCode (Q := Q)] in
theorem cutoff_description :
    (cutoff (iface := iface) rep data cost primitive).descriptionSize sizes ≤ 1024 * allowance + 1 := by
  have h := localCode_description rep data cost primitive cutoffExpression sizes allowance laws dataLaws
  have he : sizes.localSize (localCode rep data cost primitive cutoffExpression) ≤ 1024 * allowance :=
    h.trans (by simp only [cutoffExpression, Expression.descriptionBound, Expression.variableDescription]; omega)
  dsimp only [cutoff, Code.descriptionSize]
  omega

include dispatchLaws

theorem terminal_description :
    (terminal rep bd boundary data cost primitive sampler).descriptionSize sizes ≤
      (NativeComponents.finalHash rep data cost primitive sampler).descriptionSize sizes +
        sizes.localSize boundary.output + sizes.localSize boundary.optional + 4097 * allowance + 24 := by
  have hs := finishSome_description rep bd boundary data cost primitive sampler sizes allowance laws dataLaws
  have hc := cutoff_description (iface := iface) rep data cost primitive sizes allowance laws dataLaws
  have hd := dispatchLaws.distribute rep.data.unit bd.out (rep.ty storeTy)
  dsimp only [terminal, Code.descriptionSize]
  omega

def codeDescription (fuel : Nat) : Nat :=
  sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode +
    NativeHandler.codeDescription rep bd ports cost primitive uniform privatePorts sampler sizes allowance +
    NativeChallenge.descriptionBound rep cost primitive sampler sizes allowance +
    NativeCache.liveDescription rep cost primitive sizes allowance + sizes.localSize (primitive .zero) +
    sizes.localSize boundary.input + sizes.localSize boundary.output + sizes.localSize boundary.optional +
    fuel + 8192 * allowance + 128

theorem code_description (fuel : Nat) :
    (code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel).descriptionSize sizes ≤
      codeDescription rep bd boundary cost primitive sampler ports uniform privatePorts R sizes allowance fuel := by
  have hs := setup_description (iface := iface) rep bd boundary data cost primitive sizes allowance laws dataLaws
  have ht := terminal_description rep bd boundary data cost primitive sampler sizes allowance laws dataLaws dispatchLaws
  have hc := NativeHandler.caller_description rep bd ports data cost primitive uniform privatePorts sampler
    sizes allowance laws dataLaws dispatchLaws R fuel
  have hf := NativeHandler.finalHash_description rep data cost primitive sampler sizes allowance laws dataLaws
  dsimp only [code, Code.descriptionSize, codeDescription]
  omega

end Signatures.Runtime.Schnorr.ListROM.NativePass
