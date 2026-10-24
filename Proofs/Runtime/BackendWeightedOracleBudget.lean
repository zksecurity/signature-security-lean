import Proofs.Runtime.BackendWeightedHandlerState
import Proofs.Runtime.BackendWeightedHashBudget
import Proofs.Runtime.BackendWeightedSignBudget
import Proofs.Runtime.BackendWeightedHandlerBudget

/-! Complete weighted native dispatcher budgets. Both actual reply procedures
are costed from primitive contracts and preserve capacities for all remaining
adaptive requests. There is no supplied finished-handler efficiency premise. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM.NativeHandler

open BackendProgram Reply

def goodReplyTime (index : Index) (overhead : Nat → Nat)
    (width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime : Nat) : Nat :=
  let W := handlerStoreWidth index width cap
  let cacheCap := cap * (index.bound + 1)
  max (Reply.goodHashTime overhead W cacheCap topicTime indexTime natEqTime scalarTime zeroTime scaleTime)
    (Reply.goodSignTime index overhead W cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime)

def goodHandlerTime (index : Index) (overhead : Nat → Nat)
    (width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime adapterTime dynamicTime : Nat) : Nat :=
  handlerTime overhead (handlerStoreWidth index width cap)
    (goodReplyTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime) adapterTime dynamicTime

def badReplyTime (index : Index) (overhead : Nat → Nat)
    (width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime groupAddTime : Nat) : Nat :=
  let W := handlerStoreWidth index width cap
  let cacheCap := cap * (index.bound + 1)
  max (Reply.badHashTime overhead W cacheCap topicTime indexTime natEqTime scalarTime zeroTime scaleTime groupAddTime)
    (Reply.badSignTime index overhead W cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime groupAddTime)

def badHandlerTime (index : Index) (overhead : Nat → Nat)
    (width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime groupAddTime adapterTime dynamicTime : Nat) : Nat :=
  handlerTime overhead (handlerStoreWidth index width cap)
    (badReplyTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime groupAddTime) adapterTime dynamicTime

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
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)
  (dispatchLaws : DispatchCostLaws (Q := Q) overhead)

include sizes lists laws dataLaws primitiveBound mono routing dispatchLaws

theorem goodCode_bound
    (width cap remaining natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime adapterTime dynamicTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width)
    (hn : ∀ k ≤ (index.bound + 1) + index.bound + 1, Q.size rep.data.nat k ≤ width)
    (hne : ∀ j k, j ≤ (index.bound + 1) + index.bound → k ≤ (index.bound + 1) + index.bound →
      (primitiveBound .natEq).time (j, k) ≤ natEqTime)
    (hns : ∀ k ≤ index.bound + 1, (primitiveBound .natSub).time (k, 1) ≤ natSubTime)
    (hna : ∀ k ≤ index.bound + 1, (primitiveBound .natAdd).time (k, 1) ≤ natAddTime)
    (he : ∀ x y : K, Q.size (rep.ty key) x ≤ Reply.goodSignEvaluationWidth index (handlerStoreWidth index width cap) (cap * (index.bound + 1)) →
      Q.size (rep.ty key) y ≤ Reply.goodSignEvaluationWidth index (handlerStoreWidth index width cap) (cap * (index.bound + 1)) → (primitiveBound .keyEq).time (x, y) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (hdraw : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound .zero).time () ≤ zeroTime)
    (ha : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ addTime)
    (hmul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (htick : ∀ n ≤ index.bound + 1, ∀ encoded ≤ 7 * Reply.goodSignEvaluationWidth index
      (handlerStoreWidth index width cap) (cap * (index.bound + 1)), control.loop n encoded ≤ evaluatorTickTime)
    (hgen : ∀ k ≤ index.bound + 1, (primitiveBound (.finOfNat index.bound)).time k ≤ genIndexTime)
    (hfin : (primitiveBound (.finZero index.bound)).time () ≤ finZeroTime)
    (hone : (primitiveBound .one).time () ≤ oneTime)
    (hscale : ∀ r : F, ∀ g : G₁, (primitiveBound .scale₁).time (r, g) ≤ scaleTime)
    (caps : PortCaps rep index.ty index.messageTy bd ports width adapterTime)
    (samples : DynamicSamplingCaps rep index.ty index.messageTy bd ports sampler control queryCost width dynamicTime) :
    Bounds control queryCost (goodCode rep index bd ports sampler data cost primitive sampling)
      (fun p => RequestSized (Q := Q) rep index.ty index.messageTy width p.1 ∧
        ReservedState (Q := Q) rep index width cap (remaining + 1) p.2)
      (fun p => Q.size bd.idx p.1 ≤ 8 * width ∧ ReservedState (Q := Q) rep index width cap remaining p.2)
      (goodHandlerTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime adapterTime dynamicTime) := by
  let W := handlerStoreWidth index width cap
  let cacheCap := cap * (index.bound + 1)
  let replyTime := goodReplyTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime
  have h8 : 8 * width ≤ W := handlerStoreWidth_ge index width cap
  have hw : width ≤ W := by omega
  have h5 : 5 * width ≤ W := by omega
  have hs₀ := goodReserved_size rep index sizes lists width cap (remaining + 1) hh hf hg
  have hs₁ := goodReserved_size rep index sizes lists width cap remaining hh hf hg
  have hcompare : W ≤ Reply.goodSignEvaluationWidth index W cacheCap := by
    dsimp [Reply.goodSignEvaluationWidth, Evaluate.evaluationWidth]
    nlinarith
  have hashBound : Bounds control queryCost (Reply.goodHash rep data cost primitive sampling index)
      (fun p => Q.size (rep.ty index.ty) p.1 ≤ width ∧ ReservedState (Q := Q) rep index width cap (remaining + 1) p.2)
      (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧ ReservedState (Q := Q) rep index width cap remaining p.2) replyTime := by
    intro input hp out hout
    have h := Reply.goodHash_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      control queryCost routing sampling index input.1 input.2 W cacheCap topicTime indexTime natEqTime
      scalarTime zeroTime scaleTime (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw)
      (fun k hk => (hn k (by omega)).trans hw) (hp.1.trans hw) (hs₀ input.2 hp.2)
      (fun p h => (hp.2.1.1 p h).trans h5) (by have := hp.2.2.1; change _ ≤ cap * (index.bound + 1); omega)
      (fun f => (hf f).trans hw) (fun g => (hg g).trans hw)
      (fun x y hx hy => he x y (hx.trans hcompare) (hy.trans hcompare)) hi
      (fun j k hj hk => hne j k (by omega) (by omega)) hdraw hz hscale out hout
    have hs := goodHash_reserved rep index data cost primitive sampling control queryCost width cap remaining
      input.1 input.2 hp.1 hp.2 out hout
    exact ⟨⟨hg out.value.1, hs.2⟩, h.2.trans (Nat.le_max_left _ _)⟩
  have signBound : Bounds control queryCost (Reply.goodSign rep data cost primitive sampling index)
      (fun p => Q.size (rep.ty index.messageTy) p.1 ≤ width ∧ ReservedState (Q := Q) rep index width cap (remaining + 1) p.2)
      (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧ ReservedState (Q := Q) rep index width cap remaining p.2) replyTime := by
    intro input hp out hout
    have h := Reply.goodSign_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      control queryCost routing sampling index input.1 input.2 W cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime
      (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) (hp.1.trans hw) (hs₀ input.2 hp.2)
      (fun p h => (hp.2.1.1 p h).trans h5) (by have := hp.2.2.1; change _ ≤ cap * (index.bound + 1); omega)
      (fun f => (hf f).trans hw) (fun j => (hj j).trans hw) (fun k hk => (hn k hk).trans hw)
      hne hns hna he hi hdraw hz ha hmul htick hgen hfin hone (fun g => (hg g).trans hw) hscale out hout
    have hs := goodSign_reserved rep index sizes data cost primitive sampling control queryCost width cap remaining
      input.1 input.2 hp.1 hh hf hj hp.2 out hout
    exact ⟨⟨hg out.value.1, hs.2⟩, h.2.trans (Nat.le_max_right _ _)⟩
  exact code_bound rep index.ty index.messageTy bd ports sampler
    (rep.ty (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy)) control queryCost sizes mono routing laws
    (Reply.goodHash rep data cost primitive sampling index) (Reply.goodSign rep data cost primitive sampling index)
    dispatchLaws (ReservedState (Q := Q) rep index width cap (remaining + 1))
    (ReservedState (Q := Q) rep index width cap remaining) width W adapterTime dynamicTime replyTime hh h8
    hs₀ hs₁ (reserved_weaken rep index width cap remaining (remaining + 1) (by omega)) caps samples hashBound signBound

theorem badCode_bound
    (width cap remaining natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime groupAddTime adapterTime dynamicTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width)
    (hn : ∀ k ≤ (index.bound + 1) + index.bound + 1, Q.size rep.data.nat k ≤ width)
    (hne : ∀ j k, j ≤ (index.bound + 1) + index.bound → k ≤ (index.bound + 1) + index.bound →
      (primitiveBound .natEq).time (j, k) ≤ natEqTime)
    (hns : ∀ k ≤ index.bound + 1, (primitiveBound .natSub).time (k, 1) ≤ natSubTime)
    (hna : ∀ k ≤ index.bound + 1, (primitiveBound .natAdd).time (k, 1) ≤ natAddTime)
    (he : ∀ x y : K, Q.size (rep.ty key) x ≤ 3 * Reply.badSignEvaluationWidth index (handlerStoreWidth index width cap) (cap * (index.bound + 1)) →
      Q.size (rep.ty key) y ≤ 3 * Reply.badSignEvaluationWidth index (handlerStoreWidth index width cap) (cap * (index.bound + 1)) → (primitiveBound .keyEq).time (x, y) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (hdraw : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound .zero).time () ≤ zeroTime)
    (ha : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ addTime)
    (hmul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (htick : ∀ n ≤ index.bound + 1, ∀ encoded ≤ 7 * Reply.badSignEvaluationWidth index
      (handlerStoreWidth index width cap) (cap * (index.bound + 1)), control.loop n encoded ≤ evaluatorTickTime)
    (hgen : ∀ k ≤ index.bound + 1, (primitiveBound (.finOfNat index.bound)).time k ≤ genIndexTime)
    (hfin : (primitiveBound (.finZero index.bound)).time () ≤ finZeroTime)
    (hone : (primitiveBound .one).time () ≤ oneTime)
    (hscale : ∀ r : F, ∀ g : G₁, (primitiveBound .scale₁).time (r, g) ≤ scaleTime)
    (hadd : ∀ g h : G₁, (primitiveBound .add₁).time (g, h) ≤ groupAddTime)
    (caps : PortCaps rep index.ty index.messageTy bd ports width adapterTime)
    (samples : DynamicSamplingCaps rep index.ty index.messageTy bd ports sampler control queryCost width dynamicTime) :
    Bounds control queryCost (badCode rep index bd ports sampler data cost primitive sampling)
      (fun p => RequestSized (Q := Q) rep index.ty index.messageTy width p.1 ∧
        ReservedState (Q := Q) rep index width cap (remaining + 1) p.2)
      (fun p => Q.size bd.idx p.1 ≤ 8 * width ∧ ReservedState (Q := Q) rep index width cap remaining p.2)
      (badHandlerTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime groupAddTime adapterTime dynamicTime) := by
  let W := handlerStoreWidth index width cap
  let cacheCap := cap * (index.bound + 1)
  let replyTime := badReplyTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime groupAddTime
  have h8 : 8 * width ≤ W := handlerStoreWidth_ge index width cap
  have hw : width ≤ W := by omega
  have h5 : 5 * width ≤ W := by omega
  have hs₀ := badReserved_size rep index sizes lists width cap (remaining + 1) hh hf hg
  have hs₁ := badReserved_size rep index sizes lists width cap remaining hh hf hg
  have hcompare : 3 * W ≤ 3 * Reply.badSignEvaluationWidth index W cacheCap := by
    dsimp [Reply.badSignEvaluationWidth, Evaluate.evaluationWidth]
    nlinarith
  have hashBound : Bounds control queryCost (Reply.badHash rep data cost primitive sampling index)
      (fun p => Q.size (rep.ty index.ty) p.1 ≤ width ∧ ReservedState (Q := Q) rep index width cap (remaining + 1) p.2)
      (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧ ReservedState (Q := Q) rep index width cap remaining p.2) replyTime := by
    intro input hp out hout
    have h := Reply.badHash_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      control queryCost routing sampling index input.1 input.2 W cacheCap topicTime indexTime natEqTime
      scalarTime zeroTime scaleTime groupAddTime (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw)
      (fun k hk => (hn k (by omega)).trans hw) (hp.1.trans hw) (hs₀ input.2 hp.2)
      (fun p h => (hp.2.1.1 p h).trans h5) (by have := hp.2.2.1; change _ ≤ cap * (index.bound + 1); omega)
      (fun f => (hf f).trans hw) (fun g => (hg g).trans hw)
      (fun x y hx hy => he x y (hx.trans hcompare) (hy.trans hcompare)) hi
      (fun j k hj hk => hne j k (by omega) (by omega)) hdraw hz hscale hadd out hout
    have hs := badHash_reserved rep index data cost primitive sampling control queryCost width cap remaining
      input.1 input.2 hp.1 hp.2 out hout
    exact ⟨⟨hg out.value.1, hs.2⟩, h.2.trans (Nat.le_max_left _ _)⟩
  have signBound : Bounds control queryCost (Reply.badSign rep data cost primitive sampling index)
      (fun p => Q.size (rep.ty index.messageTy) p.1 ≤ width ∧ ReservedState (Q := Q) rep index width cap (remaining + 1) p.2)
      (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧ ReservedState (Q := Q) rep index width cap remaining p.2) replyTime := by
    intro input hp out hout
    have h := Reply.badSign_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      control queryCost routing sampling index input.1 input.2 W cacheCap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime groupAddTime
      (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) (hp.1.trans hw) (hs₀ input.2 hp.2)
      (fun p h => (hp.2.1.1 p h).trans h5) (by have := hp.2.2.1; change _ ≤ cap * (index.bound + 1); omega)
      (fun f => (hf f).trans hw) (fun j => (hj j).trans hw) (fun k hk => (hn k hk).trans hw)
      hne hns hna he hi hdraw hz ha hmul htick hgen hfin hone (fun g => (hg g).trans hw) hscale hadd out hout
    have hs := badSign_reserved rep index sizes data cost primitive sampling control queryCost width cap remaining
      input.1 input.2 hp.1 hh hf hj hp.2 out hout
    exact ⟨⟨hg out.value.1, hs.2⟩, h.2.trans (Nat.le_max_right _ _)⟩
  exact code_bound rep index.ty index.messageTy bd ports sampler
    (rep.ty (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy)) control queryCost sizes mono routing laws
    (Reply.badHash rep data cost primitive sampling index) (Reply.badSign rep data cost primitive sampling index)
    dispatchLaws (ReservedState (Q := Q) rep index width cap (remaining + 1))
    (ReservedState (Q := Q) rep index width cap remaining) width W adapterTime dynamicTime replyTime hh h8
    hs₀ hs₁ (reserved_weaken rep index width cap remaining (remaining + 1) (by omega)) caps samples hashBound signBound

end Signatures.Runtime.WeightedAGM.NativeHandler
