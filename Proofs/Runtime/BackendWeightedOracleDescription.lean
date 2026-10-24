import Proofs.Runtime.BackendWeightedOracle
import Proofs.Runtime.BackendWeightedReplyDescription
import Proofs.Runtime.BackendWeightedHandlerDescription

/-! Complete stored-code bounds for weighted native dispatch and the general
caller phase. Both actual replies, the degree/dimension-sized term generator,
samplers, ports, caller code and bounded-loop syntax are counted. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM.NativeHandler

open BackendProgram Reply

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M Input Output : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (index : Index)
  (bd : Boundary C (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor Input Output)
  (ports : NativePorts (Q := Q) rep index.ty index.messageTy bd) (sampler : BoundedSampler rep index.ty index.messageTy bd ports (iface := iface))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
  (dispatchLaws : DispatchDescriptionLaws (Q := Q) sizes allowance)

include laws dataLaws dispatchLaws

theorem goodCode_description :
    (goodCode rep index bd ports sampler data cost primitive sampling).descriptionSize sizes ≤
      2 * sampling.scalar.descriptionSize sizes + sampler.code.descriptionSize sizes +
      2 * sizes.localSize (primitive .keyEq) + 4 * sizes.localSize (primitive (.finVal index.bound)) +
      3 * sizes.localSize (primitive .natEq) + 4 * sizes.localSize (primitive .zero) +
      2 * sizes.localSize (primitive .scale₁) +
      1 * sizes.localSize (primitive .add) + 1 * sizes.localSize (primitive .mul) +
      sizes.localSize (primitive .natSub) + 2 * sizes.localSize (primitive .natAdd) +
      sizes.localSize (primitive (.finZero index.bound)) +
      index.termsDescription allowance (fun instr => sizes.localSize (primitive instr)) +
      sizes.localSize ports.request + sizes.localSize ports.randomTag +
      sizes.localSize ports.hashTag + sizes.localSize ports.signTag + 1800 * allowance + 240 := by
  have h := code_description (rep.ty (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy))
    sizes allowance laws rep index.ty index.messageTy bd ports sampler
    (Reply.goodHash rep data cost primitive sampling index) (Reply.goodSign rep data cost primitive sampling index) dispatchLaws
  have hh := Reply.goodHash_description rep data cost primitive sizes allowance laws dataLaws sampling index
  have hs := Reply.goodSign_description rep data cost primitive sizes allowance laws dataLaws sampling index
  exact h.trans (by omega)

theorem badCode_description :
    (badCode rep index bd ports sampler data cost primitive sampling).descriptionSize sizes ≤
      4 * sampling.scalar.descriptionSize sizes + sampler.code.descriptionSize sizes +
      2 * sizes.localSize (primitive .keyEq) + 4 * sizes.localSize (primitive (.finVal index.bound)) +
      3 * sizes.localSize (primitive .natEq) + 7 * sizes.localSize (primitive .zero) +
      6 * sizes.localSize (primitive .scale₁) +
      2 * sizes.localSize (primitive .add₁) +
      2 * sizes.localSize (primitive .add) + 2 * sizes.localSize (primitive .mul) +
      sizes.localSize (primitive .natSub) + 2 * sizes.localSize (primitive .natAdd) +
      sizes.localSize (primitive (.finZero index.bound)) +
      index.termsDescription allowance (fun instr => sizes.localSize (primitive instr)) +
      sizes.localSize ports.request + sizes.localSize ports.randomTag +
      sizes.localSize ports.hashTag + sizes.localSize ports.signTag + 1952 * allowance + 264 := by
  have h := code_description (rep.ty (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy))
    sizes allowance laws rep index.ty index.messageTy bd ports sampler
    (Reply.badHash rep data cost primitive sampling index) (Reply.badSign rep data cost primitive sampling index) dispatchLaws
  have hh := Reply.badHash_description rep data cost primitive sizes allowance laws dataLaws sampling index
  have hs := Reply.badSign_description rep data cost primitive sizes allowance laws dataLaws sampling index
  exact h.trans (by omega)

variable (R : GeneralCaller.Caller (Q := Q) (bd := bd))

theorem goodCaller_description (fuel : Nat) :
    (goodCaller rep index bd ports sampler data cost primitive sampling R fuel).descriptionSize sizes ≤
      sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode + fuel +
      2 * sampling.scalar.descriptionSize sizes + sampler.code.descriptionSize sizes +
      2 * sizes.localSize (primitive .keyEq) + 4 * sizes.localSize (primitive (.finVal index.bound)) +
      3 * sizes.localSize (primitive .natEq) + 4 * sizes.localSize (primitive .zero) +
      2 * sizes.localSize (primitive .scale₁) +
      1 * sizes.localSize (primitive .add) + 1 * sizes.localSize (primitive .mul) +
      sizes.localSize (primitive .natSub) + 2 * sizes.localSize (primitive .natAdd) +
      sizes.localSize (primitive (.finZero index.bound)) +
      index.termsDescription allowance (fun instr => sizes.localSize (primitive instr)) +
      sizes.localSize ports.request + sizes.localSize ports.randomTag +
      sizes.localSize ports.hashTag + sizes.localSize ports.signTag + 1855 * allowance + 266 := by
  have h := caller_description (rep.ty (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy))
    sizes allowance laws rep index.ty index.messageTy bd ports sampler
    (Reply.goodHash rep data cost primitive sampling index) (Reply.goodSign rep data cost primitive sampling index) dispatchLaws R fuel
  have hc := goodCode_description rep index bd ports sampler data cost primitive sampling sizes allowance laws dataLaws dispatchLaws
  dsimp only [goodCode] at hc
  exact h.trans (by omega)

theorem badCaller_description (fuel : Nat) :
    (badCaller rep index bd ports sampler data cost primitive sampling R fuel).descriptionSize sizes ≤
      sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode + fuel +
      4 * sampling.scalar.descriptionSize sizes + sampler.code.descriptionSize sizes +
      2 * sizes.localSize (primitive .keyEq) + 4 * sizes.localSize (primitive (.finVal index.bound)) +
      3 * sizes.localSize (primitive .natEq) + 7 * sizes.localSize (primitive .zero) +
      6 * sizes.localSize (primitive .scale₁) +
      2 * sizes.localSize (primitive .add₁) +
      2 * sizes.localSize (primitive .add) + 2 * sizes.localSize (primitive .mul) +
      sizes.localSize (primitive .natSub) + 2 * sizes.localSize (primitive .natAdd) +
      sizes.localSize (primitive (.finZero index.bound)) +
      index.termsDescription allowance (fun instr => sizes.localSize (primitive instr)) +
      sizes.localSize ports.request + sizes.localSize ports.randomTag +
      sizes.localSize ports.hashTag + sizes.localSize ports.signTag + 2007 * allowance + 290 := by
  have h := caller_description (rep.ty (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy))
    sizes allowance laws rep index.ty index.messageTy bd ports sampler
    (Reply.badHash rep data cost primitive sampling index) (Reply.badSign rep data cost primitive sampling index) dispatchLaws R fuel
  have hc := badCode_description rep index bd ports sampler data cost primitive sampling sizes allowance laws dataLaws dispatchLaws
  dsimp only [badCode] at hc
  exact h.trans (by omega)

end Signatures.Runtime.WeightedAGM.NativeHandler
