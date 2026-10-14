import Signatures.Runtime.BackendCoronHandler
import Signatures.Runtime.BackendCoronStateInvariant
import Signatures.Runtime.BackendDispatchBudget

/-! Native general-request costs from encoding adapters, a dynamic sampling
primitive, and the proved native hash/sign budget. All wrapper context copies,
tagging, invocation, and dispatch charges are explicit. Message types need not
be finite. Adapter caps concern only data conversion, not a whole handler. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeHandler

open BackendProgram ReplyCompiler

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁))
  (ports : NativePorts (Q := Q) rep bd)

def RequestSized (width : Nat) : GeneralRequest M randomBound → Prop
  | .inl (.inl n) => Q.size (rep.ty (boundedNat randomBound)) n ≤ width
  | .inl (.inr m) => Q.size (rep.ty message) m ≤ width
  | .inr m => Q.size (rep.ty message) m ≤ width

/-- The tag allowance includes the request and reply encodings together. It is
larger than the message cap, so tagging does not require free space or an
impossible same-width encoding for arbitrary bounded messages. -/
structure PortCaps (width adapterTime : Nat) : Prop where
  request : ∀ i, RequestSized (Q := Q) rep width i →
    Q.size bd.pos i ≤ 8 * width ∧ Q.cost ports.request i ≤ adapterTime
  randomReply : ∀ r, Q.size ports.randomReply r ≤ 8 * width
  randomTag : ∀ r, Q.size bd.idx (tagRandom r) ≤ 8 * width ∧ Q.cost ports.randomTag r ≤ adapterTime
  groupTag : ∀ signing m g, Q.size (rep.ty message) m ≤ width → Q.size (rep.ty point₁) g ≤ width →
    Q.size bd.idx (tagGroup signing (m, g)) ≤ 8 * width ∧ Q.cost (ports.groupTag signing) (m, g) ≤ adapterTime

variable {iface : Interface (C := C) unifSpec} (sampler : BoundedSampler rep bd ports (iface := iface))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

structure DynamicSamplingCaps (width samplingTime : Nat) : Prop where
  time : ∀ n, Q.size (rep.ty (boundedNat randomBound)) n ≤ width →
    ∀ z ∈ support (sampler.code.run control queryCost n), z.steps ≤ samplingTime

def GroupPre (qS width cap : Nat) (p : M × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) : Prop :=
  Q.size (rep.ty message) p.1 ≤ width ∧ StateInvariant (Q := Q) rep qS width width cap p.2

def ReplyPost (qS width cap : Nat) (p : G₁ × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) : Prop :=
  Q.size (rep.ty point₁) p.1 ≤ width ∧ StateInvariant (Q := Q) rep qS width (writtenStoreWidth width cap) (cap + 1) p.2

def HandlerPost (qS width cap : Nat) (p : GeneralIndex M G₁ randomBound ×
    (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) : Prop :=
  Q.size bd.idx p.1 ≤ 8 * width ∧ StateInvariant (Q := Q) rep qS width (writtenStoreWidth width cap) (cap + 1) p.2

variable [C.HasOption] {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)

include sizes

theorem request_size (width : Nat) (hh : header ≤ width) (i : GeneralRequest M randomBound)
    (hi : RequestSized (Q := Q) rep width i) : Q.size (generalPositions rep randomBound) i ≤ 3 * width := by
  have ho := sizes.sum_le (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty message)) (rep.ty message) i
  rcases i with (n | m) | m
  · have hn := sizes.sum_le (rep.ty (boundedNat randomBound)) (rep.ty message) (.inl n)
    dsimp only [RequestSized, generalPositions, Sum.elim_inl] at *
    omega
  · have hn := sizes.sum_le (rep.ty (boundedNat randomBound)) (rep.ty message) (.inr m)
    dsimp only [RequestSized, generalPositions, Sum.elim_inl, Sum.elim_inr] at *
    omega
  · dsimp only [RequestSized, generalPositions, Sum.elim_inr] at *
    omega

include mono routing

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

theorem random_bound (qS width cap adapterTime samplingTime : Nat) (hh : header ≤ width)
    (caps : PortCaps rep bd ports width adapterTime)
    (samples : DynamicSamplingCaps rep bd ports sampler control queryCost width samplingTime) :
    Bounds control queryCost (random rep bd ports sampler qS)
      (fun p => Q.size (rep.ty (boundedNat randomBound)) p.1 ≤ width ∧ StateInvariant (Q := Q) rep qS width width cap p.2)
      (HandlerPost (Q := Q) rep bd qS width cap)
      (samplingTime + adapterTime + 4 * overhead (32 * writtenStoreWidth width cap)) := by
  let W := writtenStoreWidth width cap
  have hw : 8 * width ≤ W := by dsimp [W, writtenStoreWidth]; nlinarith
  have hsample : Bounds control queryCost sampler.code
      (fun n => Q.size (rep.ty (boundedNat randomBound)) n ≤ width) (fun _ => True) samplingTime := by
    intro n hn z hz
    exact ⟨trivial, samples.time n hn z hz⟩
  have hfirst := Bounds.first control queryCost (rep.ty (machineStore qS)) sampler.code
    (fun n => Q.size (rep.ty (boundedNat randomBound)) n ≤ width) (fun _ => True)
    (StateInvariant (Q := Q) rep qS width width cap) samplingTime (overhead (32 * W)) hsample (by
      intro saved hs value _
      exact (routing.retain _ _).trans (mono (by have := caps.randomReply value; have := hs.1; omega)))
  have htag := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing (rep.ty (machineStore qS)) ports.randomTag
    (fun _ => True) (fun r => Q.size bd.idx r ≤ 8 * width)
    (StateInvariant (Q := Q) rep qS width width cap) W adapterTime
    (fun r _ => (caps.randomReply r).trans hw)
    (fun saved hs => hs.1.trans (by omega))
    (fun r _ => ⟨(caps.randomTag r).1, (caps.randomTag r).1.trans hw, (caps.randomTag r).2⟩)
  intro input hi z hz
  simp only [random, Code.run, sequenceRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨mid, hm, out, ho, rfl⟩ := hz
  obtain ⟨hmid, htime⟩ := hfirst input hi mid hm
  obtain ⟨hout, htagTime⟩ := htag mid.value hmid out ho
  have hseq := routing.sequence
    (Q.size (StepClass.HasProd.prod (rep.ty (boundedNat randomBound)) (rep.ty (machineStore qS))) input)
    (Q.size (StepClass.HasProd.prod ports.randomReply (rep.ty (machineStore qS))) mid.value)
  have hin := sizes.prod_le (rep.ty (boundedNat randomBound)) (rep.ty (machineStore qS)) input
  have hms := sizes.prod_le ports.randomReply (rep.ty (machineStore qS)) mid.value
  have hinput := hi.1
  have his := hi.2.1
  have hmidstore := hmid.2.1
  have hmidreply := caps.randomReply mid.value.1
  have hfee := mono (show
      Q.size (StepClass.HasProd.prod (rep.ty (boundedNat randomBound)) (rep.ty (machineStore qS))) input +
      Q.size (StepClass.HasProd.prod ports.randomReply (rep.ty (machineStore qS))) mid.value ≤ 32 * W by omega)
  dsimp only [W] at *
  exact ⟨⟨hout.1, hout.2.1.trans (by omega), hout.2.2.1, hout.2.2.2.trans (Nat.le_succ cap)⟩, by
    omega⟩

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [Field F] [SampleableType F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (localLaws : LocalCostLaws Q overhead)

include localLaws

/-- Add only request retention and tagging to an already proved reply budget.
The complete dispatcher theorem below instantiates this premise with the native
reply theorem derived from primitive contracts. -/
theorem group_bound (qS : Nat) (signing : Bool) (width cap adapterTime replyTime : Nat)
    (hh : header ≤ width) (caps : PortCaps rep bd ports width adapterTime)
    (hb : Bounds control queryCost (backendReply rep data samplingCode cost primitive qS signing)
      (GroupPre (Q := Q) rep qS width cap) (ReplyPost (Q := Q) rep qS width cap) replyTime) :
    Bounds control queryCost (group rep bd ports data samplingCode cost primitive qS signing)
      (GroupPre (Q := Q) rep qS width cap) (HandlerPost (Q := Q) rep bd qS width cap)
      (replyTime + adapterTime + 26 * overhead (32 * writtenStoreWidth width cap)) := by
  let W := writtenStoreWidth width cap
  have hw : 8 * width ≤ W := by dsimp [W, writtenStoreWidth]; nlinarith
  let pre := GroupPre (Q := Q) rep qS width cap
  let post := ReplyPost (Q := Q) rep qS width cap
  let keep := fun m : M => Q.size (rep.ty message) m ≤ width
  have hc := Language.withContext_bound_of_width sizes localLaws mono control queryCost routing
    (rep.ty (machineStore qS)) (Q.identity (rep.ty message))
    (backendReply rep data samplingCode cost primitive qS signing) pre post keep W
    (overhead (32 * W)) replyTime (by omega)
    (by
      intro p hp
      exact ⟨hp.1.trans (by omega), hp.2.1.trans (by omega), hp.1.trans (by omega), hp.1,
        (localLaws.identity _ _).trans (mono (by have := hp.1; omega))⟩)
    (by intro p hp; exact ⟨hp.1.trans (by omega), hp.2.1⟩) hb
  let tagCode := Q.compose
    (QP.pair (QP.snd (rep.ty point₁) (rep.ty message)) (QP.fst (rep.ty point₁) (rep.ty message)))
    (ports.groupTag signing)
  have ht : ∀ p : G₁ × M, Q.size (rep.ty point₁) p.1 ≤ width → Q.size (rep.ty message) p.2 ≤ width →
      Q.cost tagCode p ≤ adapterTime + 4 * overhead (32 * W) := by
    intro p hg hm
    have htag := (caps.groupTag signing p.2 p.1 hm hg)
    have hpair1 := sizes.prod_le (rep.ty point₁) (rep.ty message) p
    have hpair2 := sizes.prod_le (rep.ty message) (rep.ty point₁) (p.2, p.1)
    have hfst := localLaws.fst (rep.ty point₁) (rep.ty message) p
    have hsnd := localLaws.snd (rep.ty point₁) (rep.ty message) p
    have hpair := localLaws.pair (QP.snd (rep.ty point₁) (rep.ty message))
      (QP.fst (rep.ty point₁) (rep.ty message)) p
    have hcompose := localLaws.compose
      (QP.pair (QP.snd (rep.ty point₁) (rep.ty message)) (QP.fst (rep.ty point₁) (rep.ty message)))
      (ports.groupTag signing) p
    have hfee : ∀ n ≤ 32 * W, overhead n ≤ overhead (32 * W) := fun _ hn => mono hn
    dsimp only [tagCode] at *
    grind only
  have htag := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing
    (rep.ty (machineStore qS)) tagCode
    (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧ Q.size (rep.ty message) p.2 ≤ width)
    (fun r => Q.size bd.idx r ≤ 8 * width)
    (StateInvariant (Q := Q) rep qS width W (cap + 1)) W
    (adapterTime + 4 * overhead (32 * W))
    (by intro p hp; have := sizes.prod_le (rep.ty point₁) (rep.ty message) p; omega)
    (fun _ hs => hs.1)
    (by
      intro p hp
      have h := caps.groupTag signing p.2 p.1 hp.2 hp.1
      exact ⟨h.1, h.1.trans hw, ht p hp.1 hp.2⟩)
  intro input hi z hz
  simp only [group, Code.run, sequenceRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨mid, hm, out, ho, rfl⟩ := hz
  obtain ⟨hmid, htime⟩ := hc input hi mid hm
  obtain ⟨hout, htagTime⟩ := htag mid.value ⟨⟨hmid.1.1, hmid.2⟩, hmid.1.2⟩ out ho
  have hin := sizes.prod_le (rep.ty message) (rep.ty (machineStore qS)) input
  have hm1 := sizes.prod_le (rep.ty point₁) (rep.ty message) mid.value.1
  have hm2 := sizes.prod_le (StepClass.HasProd.prod (rep.ty point₁) (rep.ty message)) (rep.ty (machineStore qS)) mid.value
  have his := hi.2.1
  have him := hi.1
  have hmg := hmid.1.1
  have hmm := hmid.2
  have hms := hmid.1.2.1
  have hseq := routing.sequence
    (Q.size (StepClass.HasProd.prod (rep.ty message) (rep.ty (machineStore qS))) input)
    (Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod (rep.ty point₁) (rep.ty message)) (rep.ty (machineStore qS))) mid.value)
  have hfee := mono (show Q.size (StepClass.HasProd.prod (rep.ty message) (rep.ty (machineStore qS))) input +
      Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod (rep.ty point₁) (rep.ty message)) (rep.ty (machineStore qS))) mid.value ≤
        32 * W by dsimp only [pre, post, keep, GroupPre, ReplyPost] at *; omega)
  dsimp only [W] at *
  exact ⟨hout, by omega⟩

def nativeHandlerTime (overhead : Nat → Nat)
    (width cap comparisonTime scalarTime coinTime opTime adapterTime dynamicTime : Nat) : Nat :=
  nativeReplyTime overhead width cap comparisonTime scalarTime coinTime opTime + dynamicTime +
    2 * adapterTime + 40 * overhead (32 * writtenStoreWidth width cap)

variable [QO : Q.HasOption] [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  (dispatchLaws : DispatchCostLaws (Q := Q) overhead)
  (lists : ListSizeLaws Q rep.data header) (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))

include dispatchLaws lists dataLaws

/-- The complete native handler budget is derived from local data adapters,
primitive sampling, group/field operations, and encoded-size laws. It does not
assume a runtime bound on the completed dispatcher. -/
theorem code_bound (qS width cap comparisonTime scalarTime coinTime opTime adapterTime dynamicTime : Nat)
    (hh : header ≤ width) (caps : PortCaps rep bd ports width adapterTime)
    (dynamicSamples : DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime)
    (values : NativeValueCaps (Q := Q) rep qS width)
    (ops : NativeInstructionCaps rep cost primitive primitiveBound qS width comparisonTime opTime)
    (samples : NativeSamplingCaps rep samplingCode control queryCost qS scalarTime coinTime) :
    Bounds control queryCost (code rep bd ports sampler data samplingCode cost primitive qS)
      (fun p => RequestSized (Q := Q) rep width p.1 ∧ StateInvariant (Q := Q) rep qS width width cap p.2)
      (HandlerPost (Q := Q) rep bd qS width cap)
      (nativeHandlerTime overhead width cap comparisonTime scalarTime coinTime opTime adapterTime dynamicTime) := by
  let W := writtenStoreWidth width cap
  let R := overhead (32 * W)
  let replyTime := nativeReplyTime overhead width cap comparisonTime scalarTime coinTime opTime
  have hw : 8 * width ≤ W := by dsimp [W, writtenStoreWidth]; nlinarith
  have hr := random_bound rep bd ports sampler control queryCost sizes mono routing
    qS width cap adapterTime dynamicTime hh caps dynamicSamples
  have hg := fun signing => group_bound rep bd ports control queryCost sizes mono routing
    data samplingCode cost primitive localLaws qS signing width cap adapterTime replyTime hh caps
    (backendReply_invariant_bound rep data samplingCode cost primitive control queryCost sizes lists
      localLaws dataLaws primitiveBound mono routing qS signing width cap comparisonTime scalarTime coinTime opTime
      hh values ops samples)
  let preR := fun p : Fin (randomBound + 1) × (machineStore qS).Value (cryptoBase F G₁ G₂ M M) =>
    Q.size (rep.ty (boundedNat randomBound)) p.1 ≤ width ∧ StateInvariant (Q := Q) rep qS width width cap p.2
  let preG := GroupPre (Q := Q) rep qS width cap
  let preI := fun p : (Fin (randomBound + 1) ⊕ M) × (machineStore qS).Value (cryptoBase F G₁ G₂ M M) =>
    Sum.elim (fun n => preR (n, p.2)) (fun m => preG (m, p.2)) p.1
  let post := HandlerPost (Q := Q) rep bd qS width cap
  have hi : Bounds control queryCost (inner rep bd ports sampler data samplingCode cost primitive qS)
      preI post (max (dynamicTime + adapterTime + 4 * R) (replyTime + adapterTime + 26 * R) + 4 * R) :=
    branchStore_bound_of_width sizes mono control queryCost routing dispatchLaws (rep.ty (machineStore qS))
      (random rep bd ports sampler qS) (group rep bd ports data samplingCode cost primitive qS false)
      preR preG post W _ _ (by omega)
      (fun p hp => ⟨hp.1.trans (by omega), hp.2.1.trans (by omega)⟩)
      (fun p hp => ⟨hp.1.trans (by omega), hp.2.1.trans (by omega)⟩) hr (hg false)
  have hinnerSize : ∀ p, preI p →
      Q.size (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty message)) p.1 ≤ W ∧
      Q.size (rep.ty (machineStore qS)) p.2 ≤ W := by
    rintro ⟨i, saved⟩ hp
    have hs := sizes.sum_le (rep.ty (boundedNat randomBound)) (rep.ty message) i
    cases i with
    | inl n =>
        have hm := hp.1
        have ht := hp.2.1
        dsimp only [Sum.elim_inl] at hs
        dsimp only at hm ht ⊢
        exact ⟨by omega, ht.trans (by omega)⟩
    | inr m =>
        have hm := hp.1
        have ht := hp.2.1
        dsimp only [Sum.elim_inr] at hs
        dsimp only at hm ht ⊢
        exact ⟨by omega, ht.trans (by omega)⟩
  let preO := fun p : GeneralRequest M randomBound × (machineStore qS).Value (cryptoBase F G₁ G₂ M M) =>
    Sum.elim (fun i => preI (i, p.2)) (fun m => preG (m, p.2)) p.1
  have ho : Bounds control queryCost (dispatch rep bd ports sampler data samplingCode cost primitive qS)
      preO post (max (max (dynamicTime + adapterTime + 4 * R) (replyTime + adapterTime + 26 * R) + 4 * R)
        (replyTime + adapterTime + 26 * R) + 4 * R) :=
    branchStore_bound_of_width sizes mono control queryCost routing dispatchLaws (rep.ty (machineStore qS))
      (inner rep bd ports sampler data samplingCode cost primitive qS)
      (group rep bd ports data samplingCode cost primitive qS true) preI preG post W _ _ (by omega)
      hinnerSize (fun p hp => ⟨hp.1.trans (by omega), hp.2.1.trans (by omega)⟩) hi (hg true)
  have he := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing
    (rep.ty (machineStore qS)) ports.request (RequestSized (Q := Q) rep width)
    (RequestSized (Q := Q) rep width) (StateInvariant (Q := Q) rep qS width width cap) W adapterTime
    (fun i hi => (caps.request i hi).1.trans hw) (fun saved hs => hs.1.trans (by omega))
    (fun i hi => ⟨hi, (request_size rep sizes width hh i hi).trans (by omega), (caps.request i hi).2⟩)
  have hpre : ∀ p : GeneralRequest M randomBound × (machineStore qS).Value (cryptoBase F G₁ G₂ M M),
      RequestSized (Q := Q) rep width p.1 ∧ StateInvariant (Q := Q) rep qS width width cap p.2 → preO p := by
    rintro ⟨i, saved⟩ hp
    rcases i with (n | m) | m <;> exact hp
  intro input hp z hz
  simp only [code, Code.run, sequenceRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨mid, hm, out, hout, rfl⟩ := hz
  obtain ⟨hmid, heTime⟩ := he input hp mid hm
  obtain ⟨hpost, hoTime⟩ := ho mid.value (hpre mid.value hmid) out hout
  have hin := sizes.prod_le bd.pos (rep.ty (machineStore qS)) input
  have hmSize := sizes.prod_le (generalPositions rep randomBound) (rep.ty (machineStore qS)) mid.value
  have hinPos := (caps.request input.1 hp.1).1
  have hinStore := hp.2.1
  have hmPos := request_size rep sizes width hh mid.value.1 hmid.1
  have hmStore := hmid.2.1
  have hseq := routing.sequence
    (Q.size (StepClass.HasProd.prod bd.pos (rep.ty (machineStore qS))) input)
    (Q.size (StepClass.HasProd.prod (generalPositions rep randomBound) (rep.ty (machineStore qS))) mid.value)
  have hfee := mono (show Q.size (StepClass.HasProd.prod bd.pos (rep.ty (machineStore qS))) input +
      Q.size (StepClass.HasProd.prod (generalPositions rep randomBound) (rep.ty (machineStore qS))) mid.value ≤
        32 * W by omega)
  dsimp only [W, R, replyTime, nativeHandlerTime] at *
  exact ⟨hpost, by omega⟩

end Signatures.Runtime.Coron.NativeHandler
