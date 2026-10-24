import Proofs.Runtime.BackendLazyAGMHandler
import Proofs.Runtime.BackendLazyAGMReplyDescription
import Proofs.Runtime.BackendSignatureHandlerDescription

/-! Complete stored-code bounds for both native lazy AGM dispatchers, obtained
from actual reply descriptions and the common request-routing code. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.LazyAGM.NativeHandler

open BackendProgram Coron

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ M Input Output : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor Input Output)
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
  (dispatchLaws : DispatchDescriptionLaws (Q := Q) sizes allowance)

include laws dataLaws dispatchLaws

theorem goodCode_description :
    (goodCode rep bd ports sampler data cost primitive sampling).descriptionSize sizes ≤
      2 * sampling.scalar.descriptionSize sizes + sampler.code.descriptionSize sizes +
      2 * sizes.localSize (primitive .messageEq) + 2 * sizes.localSize (primitive .zero) +
      2 * sizes.localSize (primitive .scale₁) + sizes.localSize ports.request +
      sizes.localSize ports.randomTag + sizes.localSize (ports.groupTag false) +
      sizes.localSize (ports.groupTag true) + 840 * allowance + 112 := by
  have h := SignatureHandler.code_description rep bd ports sampler (rep.ty (storeTy scalar goodConfigTy))
    (backendGoodReply rep data cost primitive sampling) sizes allowance laws dispatchLaws
  have hh := backendGoodReply_description rep data cost primitive sizes allowance laws dataLaws sampling false
  have hs := backendGoodReply_description rep data cost primitive sizes allowance laws dataLaws sampling true
  exact h.trans (by omega)

theorem badCode_description :
    (badCode rep bd ports sampler data cost primitive sampling).descriptionSize sizes ≤
      4 * sampling.scalar.descriptionSize sizes + sampler.code.descriptionSize sizes +
      2 * sizes.localSize (primitive .messageEq) + 4 * sizes.localSize (primitive .zero) +
      6 * sizes.localSize (primitive .scale₁) + 2 * sizes.localSize (primitive .add₁) +
      sizes.localSize ports.request + sizes.localSize ports.randomTag +
      sizes.localSize (ports.groupTag false) + sizes.localSize (ports.groupTag true) + 940 * allowance + 132 := by
  have h := SignatureHandler.code_description rep bd ports sampler (rep.ty (storeTy (.pair scalar scalar) badConfigTy))
    (backendBadReply rep data cost primitive sampling) sizes allowance laws dispatchLaws
  have hh := backendBadReply_description rep data cost primitive sizes allowance laws dataLaws sampling false
  have hs := backendBadReply_description rep data cost primitive sizes allowance laws dataLaws sampling true
  exact h.trans (by omega)

variable (R : GeneralCaller.Caller (Q := Q) (bd := bd))

theorem goodCaller_description (fuel : Nat) :
    (goodCaller rep bd ports sampler data cost primitive sampling R fuel).descriptionSize sizes ≤
      sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode + fuel +
      2 * sampling.scalar.descriptionSize sizes + sampler.code.descriptionSize sizes +
      2 * sizes.localSize (primitive .messageEq) + 2 * sizes.localSize (primitive .zero) +
      2 * sizes.localSize (primitive .scale₁) + sizes.localSize ports.request +
      sizes.localSize ports.randomTag + sizes.localSize (ports.groupTag false) +
      sizes.localSize (ports.groupTag true) + 895 * allowance + 138 := by
  have h := SignatureHandler.caller_description rep bd ports sampler (rep.ty (storeTy scalar goodConfigTy))
    (backendGoodReply rep data cost primitive sampling) sizes allowance laws dispatchLaws R fuel
  have hc := goodCode_description rep bd ports sampler data cost primitive sampling sizes allowance laws dataLaws dispatchLaws
  dsimp only [goodCode] at hc
  exact h.trans (by omega)

theorem badCaller_description (fuel : Nat) :
    (badCaller rep bd ports sampler data cost primitive sampling R fuel).descriptionSize sizes ≤
      sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode + fuel +
      4 * sampling.scalar.descriptionSize sizes + sampler.code.descriptionSize sizes +
      2 * sizes.localSize (primitive .messageEq) + 4 * sizes.localSize (primitive .zero) +
      6 * sizes.localSize (primitive .scale₁) + 2 * sizes.localSize (primitive .add₁) +
      sizes.localSize ports.request + sizes.localSize ports.randomTag +
      sizes.localSize (ports.groupTag false) + sizes.localSize (ports.groupTag true) + 995 * allowance + 158 := by
  have h := SignatureHandler.caller_description rep bd ports sampler (rep.ty (storeTy (.pair scalar scalar) badConfigTy))
    (backendBadReply rep data cost primitive sampling) sizes allowance laws dispatchLaws R fuel
  have hc := badCode_description rep bd ports sampler data cost primitive sampling sizes allowance laws dataLaws dispatchLaws
  dsimp only [badCode] at hc
  exact h.trans (by omega)

end Signatures.Runtime.LazyAGM.NativeHandler
