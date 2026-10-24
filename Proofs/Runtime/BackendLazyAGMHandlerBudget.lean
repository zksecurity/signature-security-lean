import Proofs.Runtime.BackendLazyAGMHandlerState
import Proofs.Runtime.BackendLazyAGMReplyBudget
import Proofs.Runtime.BackendSignatureHandlerBudget

/-! Complete good/bad native AGM dispatcher budgets. Both instantiate the
shared routing certificate with the actual primitive-derived reply bounds and
remaining-request state invariants. No completed-handler cost is assumed. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.LazyAGM.NativeHandler

open BackendProgram Coron

def goodReplyTime (overhead : Nat → Nat)
    (width cap comparisonTime scalarTime zeroTime scaleTime : Nat) : Nat :=
  let fee := overhead (64 * replyWidth (handlerStoreWidth width cap) cap)
  cap * (comparisonTime + 257 * fee) + scalarTime + zeroTime + scaleTime + 384 * fee

def badReplyTime (overhead : Nat → Nat)
    (width cap comparisonTime scalarTime zeroTime scaleTime addTime : Nat) : Nat :=
  let fee := overhead (64 * replyWidth (3 * handlerStoreWidth width cap) cap)
  cap * (comparisonTime + 257 * fee) + 2 * scalarTime + 2 * zeroTime + 3 * scaleTime + addTime + 468 * fee

def goodHandlerTime (overhead : Nat → Nat)
    (width cap comparisonTime scalarTime zeroTime scaleTime adapterTime dynamicTime : Nat) : Nat :=
  SignatureHandler.handlerTime overhead (handlerStoreWidth width cap)
    (goodReplyTime overhead width cap comparisonTime scalarTime zeroTime scaleTime) adapterTime dynamicTime

def badHandlerTime (overhead : Nat → Nat)
    (width cap comparisonTime scalarTime zeroTime scaleTime addTime adapterTime dynamicTime : Nat) : Nat :=
  SignatureHandler.handlerTime overhead (handlerStoreWidth width cap)
    (badReplyTime overhead width cap comparisonTime scalarTime zeroTime scaleTime addTime) adapterTime dynamicTime

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
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)
  (dispatchLaws : DispatchCostLaws (Q := Q) overhead)

include sizes lists laws dataLaws primitiveBound mono routing dispatchLaws

theorem goodCode_bound (width cap remaining comparisonTime scalarTime zeroTime scaleTime adapterTime dynamicTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (he : ∀ x y : M,
      Q.size (rep.ty message) x ≤ 5 * handlerStoreWidth width cap →
      Q.size (rep.ty message) y ≤ 5 * handlerStoreWidth width cap →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (hscale : ∀ f : F, ∀ g : G₁, (primitiveBound CryptoOp.scale₁).time (f, g) ≤ scaleTime)
    (caps : SignatureHandler.PortCaps rep bd ports width adapterTime)
    (dynamicSamples : SignatureHandler.DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime) :
    Bounds control queryCost (goodCode rep bd ports sampler data cost primitive sampling)
      (fun p => SignatureHandler.RequestSized (Q := Q) rep width p.1 ∧
        ReservedState (Q := Q) rep width cap (remaining + 1) p.2)
      (fun p => Q.size bd.idx p.1 ≤ 8 * width ∧ ReservedState (Q := Q) rep width cap remaining p.2)
      (goodHandlerTime overhead width cap comparisonTime scalarTime zeroTime scaleTime adapterTime dynamicTime) := by
  let W := handlerStoreWidth width cap
  have hw : width ≤ W := by dsimp [W, handlerStoreWidth]; nlinarith
  have h8 : 8 * width ≤ W := by dsimp [W, handlerStoreWidth]; nlinarith
  have hs₀ := goodReserved_size rep sizes lists width cap (remaining + 1) hh hf hg
  have hs₁ := goodReserved_size rep sizes lists width cap remaining hh hf hg
  have hreply : ∀ signing, Bounds control queryCost (backendGoodReply rep data cost primitive sampling signing)
      (fun p => Q.size (rep.ty message) p.1 ≤ width ∧ ReservedState (Q := Q) rep width cap (remaining + 1) p.2)
      (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧ ReservedState (Q := Q) rep width cap remaining p.2)
      (goodReplyTime overhead width cap comparisonTime scalarTime zeroTime scaleTime) := by
    intro signing input hi out hout
    have h := backendGoodReply_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      control queryCost routing sampling signing input.1 input.2 W cap comparisonTime scalarTime zeroTime scaleTime
      (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) (hi.1.trans hw) (hs₀ input.2 hi.2)
      (fun p hp => (hi.2.1.1 p hp).trans hw) (by have := hi.2.2.1; omega)
      (fun f => (hf f).trans hw) (fun g => (hg g).trans hw) he hsample hz hscale out hout
    have hstate := goodReply_reserved rep data cost primitive sampling control queryCost
      width cap remaining signing input.1 input.2 hi.1 hi.2 out hout
    exact ⟨⟨hg out.value.1, hstate.2⟩, h.2⟩
  exact SignatureHandler.code_bound rep bd ports sampler (rep.ty (storeTy scalar goodConfigTy))
    control queryCost sizes mono routing (backendGoodReply rep data cost primitive sampling) laws dispatchLaws
    (ReservedState (Q := Q) rep width cap (remaining + 1)) (ReservedState (Q := Q) rep width cap remaining)
    width W adapterTime dynamicTime (goodReplyTime overhead width cap comparisonTime scalarTime zeroTime scaleTime)
    hh h8 hs₀ hs₁ (reserved_weaken rep width cap remaining (remaining + 1) (by omega)) caps dynamicSamples hreply

theorem badCode_bound (width cap remaining comparisonTime scalarTime zeroTime scaleTime addTime adapterTime dynamicTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (he : ∀ x y : M,
      Q.size (rep.ty message) x ≤ 15 * handlerStoreWidth width cap →
      Q.size (rep.ty message) y ≤ 15 * handlerStoreWidth width cap →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (hscale : ∀ f : F, ∀ g : G₁, (primitiveBound CryptoOp.scale₁).time (f, g) ≤ scaleTime)
    (hadd : ∀ g h : G₁, (primitiveBound CryptoOp.add₁).time (g, h) ≤ addTime)
    (caps : SignatureHandler.PortCaps rep bd ports width adapterTime)
    (dynamicSamples : SignatureHandler.DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime) :
    Bounds control queryCost (badCode rep bd ports sampler data cost primitive sampling)
      (fun p => SignatureHandler.RequestSized (Q := Q) rep width p.1 ∧
        ReservedState (Q := Q) rep width cap (remaining + 1) p.2)
      (fun p => Q.size bd.idx p.1 ≤ 8 * width ∧ ReservedState (Q := Q) rep width cap remaining p.2)
      (badHandlerTime overhead width cap comparisonTime scalarTime zeroTime scaleTime addTime adapterTime dynamicTime) := by
  let W := handlerStoreWidth width cap
  have hw : width ≤ W := by dsimp [W, handlerStoreWidth]; nlinarith
  have h8 : 8 * width ≤ W := by dsimp [W, handlerStoreWidth]; nlinarith
  have hs₀ := badReserved_size rep sizes lists width cap (remaining + 1) hh hf hg
  have hs₁ := badReserved_size rep sizes lists width cap remaining hh hf hg
  have hreply : ∀ signing, Bounds control queryCost (backendBadReply rep data cost primitive sampling signing)
      (fun p => Q.size (rep.ty message) p.1 ≤ width ∧ ReservedState (Q := Q) rep width cap (remaining + 1) p.2)
      (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧ ReservedState (Q := Q) rep width cap remaining p.2)
      (badReplyTime overhead width cap comparisonTime scalarTime zeroTime scaleTime addTime) := by
    intro signing input hi out hout
    have h := backendBadReply_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      control queryCost routing sampling signing input.1 input.2 W cap comparisonTime scalarTime zeroTime scaleTime addTime
      (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) (hi.1.trans hw) (hs₀ input.2 hi.2)
      (fun p hp => (hi.2.1.1 p hp).trans hw) (by have := hi.2.2.1; omega)
      (fun f => (hf f).trans hw) (fun g => (hg g).trans hw) he hsample hz hscale hadd out hout
    have hstate := badReply_reserved rep data cost primitive sampling control queryCost
      width cap remaining signing input.1 input.2 hi.1 hi.2 out hout
    exact ⟨⟨hg out.value.1, hstate.2⟩, h.2⟩
  exact SignatureHandler.code_bound rep bd ports sampler (rep.ty (storeTy (.pair scalar scalar) badConfigTy))
    control queryCost sizes mono routing (backendBadReply rep data cost primitive sampling) laws dispatchLaws
    (ReservedState (Q := Q) rep width cap (remaining + 1)) (ReservedState (Q := Q) rep width cap remaining)
    width W adapterTime dynamicTime (badReplyTime overhead width cap comparisonTime scalarTime zeroTime scaleTime addTime)
    hh h8 hs₀ hs₁ (reserved_weaken rep width cap remaining (remaining + 1) (by omega)) caps dynamicSamples hreply

end Signatures.Runtime.LazyAGM.NativeHandler
