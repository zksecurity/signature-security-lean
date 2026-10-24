import Proofs.Runtime.BackendSignatureHandler
import Proofs.Runtime.BackendDispatchBudget

/-! Routing costs for the shared native random/hash/sign dispatcher. A reduction
instantiates the reply budget with its own primitive-derived certificate. Data
ports have individual encoding/time contracts; store predicates can track
remaining fuel, cache provenance, and chronological transcript growth. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SignatureHandler

open BackendProgram Coron

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M Input Output S : Type} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor Input Output)
  (ports : NativePorts (Q := Q) rep bd)

def RequestSized (width : Nat) : GeneralRequest M randomBound → Prop
  | .inl (.inl n) => Q.size (rep.ty (boundedNat randomBound)) n ≤ width
  | .inl (.inr m) => Q.size (rep.ty message) m ≤ width
  | .inr m => Q.size (rep.ty message) m ≤ width

structure PortCaps (width adapterTime : Nat) : Prop where
  request : ∀ i, RequestSized (Q := Q) rep width i →
    Q.size bd.pos i ≤ 8 * width ∧ Q.cost ports.request i ≤ adapterTime
  randomReply : ∀ r, Q.size ports.randomReply r ≤ 8 * width
  randomTag : ∀ r, Q.size bd.idx (tagRandom r) ≤ 8 * width ∧ Q.cost ports.randomTag r ≤ adapterTime
  groupTag : ∀ signing m g, Q.size (rep.ty message) m ≤ width → Q.size (rep.ty point₁) g ≤ width →
    Q.size bd.idx (tagGroup signing (m, g)) ≤ 8 * width ∧ Q.cost (ports.groupTag signing) (m, g) ≤ adapterTime

variable {iface : Interface (C := C) unifSpec} (sampler : BoundedSampler rep bd ports (iface := iface))
  (store : C.Str S) (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

structure DynamicSamplingCaps (width samplingTime : Nat) : Prop where
  time : ∀ n, Q.size (rep.ty (boundedNat randomBound)) n ≤ width →
    ∀ z ∈ support (sampler.code.run control queryCost n), z.steps ≤ samplingTime

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

theorem random_bound (pre post : S → Prop) (width frameWidth adapterTime samplingTime : Nat)
    (hh : header ≤ width) (hw : 8 * width ≤ frameWidth)
    (hstore : ∀ s, pre s → Q.size store s ≤ frameWidth)
    (hpreserve : ∀ s, pre s → post s)
    (caps : PortCaps rep bd ports width adapterTime)
    (samples : DynamicSamplingCaps rep bd ports sampler control queryCost width samplingTime) :
    Bounds control queryCost (random rep bd ports sampler store)
      (fun p => Q.size (rep.ty (boundedNat randomBound)) p.1 ≤ width ∧ pre p.2)
      (fun p => Q.size bd.idx p.1 ≤ 8 * width ∧ post p.2)
      (samplingTime + adapterTime + 4 * overhead (32 * frameWidth)) := by
  let fee := overhead (32 * frameWidth)
  have hsample : Bounds control queryCost sampler.code
      (fun n => Q.size (rep.ty (boundedNat randomBound)) n ≤ width) (fun _ => True) samplingTime := by
    intro n hn z hz
    exact ⟨trivial, samples.time n hn z hz⟩
  have hfirst := Bounds.first control queryCost store sampler.code
    (fun n => Q.size (rep.ty (boundedNat randomBound)) n ≤ width) (fun _ => True)
    pre samplingTime fee hsample (by
      intro saved hs value _
      exact (routing.retain _ _).trans (mono (by have := caps.randomReply value; have := hstore saved hs; omega)))
  have htag := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing store ports.randomTag
    (fun _ => True) (fun r => Q.size bd.idx r ≤ 8 * width) pre frameWidth adapterTime
    (fun r _ => (caps.randomReply r).trans hw) hstore
    (fun r _ => ⟨(caps.randomTag r).1, (caps.randomTag r).1.trans hw, (caps.randomTag r).2⟩)
  intro input hi z hz
  simp only [random, Code.run, sequenceRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨mid, hm, out, ho, rfl⟩ := hz
  obtain ⟨hmid, htime⟩ := hfirst input hi mid hm
  obtain ⟨hout, htagTime⟩ := htag mid.value hmid out ho
  have hseq := routing.sequence
    (Q.size (StepClass.HasProd.prod (rep.ty (boundedNat randomBound)) store) input)
    (Q.size (StepClass.HasProd.prod ports.randomReply store) mid.value)
  have hin := sizes.prod_le (rep.ty (boundedNat randomBound)) store input
  have hms := sizes.prod_le ports.randomReply store mid.value
  have hinput := hi.1
  have his := hstore input.2 hi.2
  have hmidstore := hstore mid.value.2 hmid.2
  have hmidreply := caps.randomReply mid.value.1
  have hfee := mono (show
    Q.size (StepClass.HasProd.prod (rep.ty (boundedNat randomBound)) store) input +
    Q.size (StepClass.HasProd.prod ports.randomReply store) mid.value ≤ 32 * frameWidth by omega)
  exact ⟨⟨hout.1, hpreserve out.value.2 hout.2⟩, by dsimp only [fee] at *; omega⟩

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  (reply : (signing : Bool) → Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.ty message) store) (StepClass.HasProd.prod (rep.ty point₁) store))
  (localLaws : LocalCostLaws Q overhead)

include localLaws

theorem group_bound (signing : Bool) (pre post : S → Prop) (width frameWidth adapterTime replyTime : Nat)
    (hh : header ≤ width) (hw : 8 * width ≤ frameWidth)
    (hpre : ∀ s, pre s → Q.size store s ≤ frameWidth)
    (hpost : ∀ s, post s → Q.size store s ≤ frameWidth)
    (caps : PortCaps rep bd ports width adapterTime)
    (hb : Bounds control queryCost (reply signing)
      (fun p => Q.size (rep.ty message) p.1 ≤ width ∧ pre p.2)
      (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧ post p.2) replyTime) :
    Bounds control queryCost (group rep bd ports store reply signing)
      (fun p => Q.size (rep.ty message) p.1 ≤ width ∧ pre p.2)
      (fun p => Q.size bd.idx p.1 ≤ 8 * width ∧ post p.2)
      (replyTime + adapterTime + 26 * overhead (32 * frameWidth)) := by
  let fee := overhead (32 * frameWidth)
  let pre' := fun p : M × S => Q.size (rep.ty message) p.1 ≤ width ∧ pre p.2
  let post' := fun p : G₁ × S => Q.size (rep.ty point₁) p.1 ≤ width ∧ post p.2
  let keep := fun m : M => Q.size (rep.ty message) m ≤ width
  have hc := Language.withContext_bound_of_width sizes localLaws mono control queryCost routing
    store (Q.identity (rep.ty message)) (reply signing) pre' post' keep frameWidth fee replyTime (by omega)
    (by
      intro p hp
      exact ⟨hp.1.trans (by omega), hpre p.2 hp.2, hp.1.trans (by omega), hp.1,
        (localLaws.identity _ _).trans (mono (by have := hp.1; omega))⟩)
    (by intro p hp; exact ⟨hp.1.trans (by omega), hpost p.2 hp.2⟩) hb
  let tagCode := Q.compose
    (QP.pair (QP.snd (rep.ty point₁) (rep.ty message)) (QP.fst (rep.ty point₁) (rep.ty message)))
    (ports.groupTag signing)
  have ht : ∀ p : G₁ × M, Q.size (rep.ty point₁) p.1 ≤ width → Q.size (rep.ty message) p.2 ≤ width →
      Q.cost tagCode p ≤ adapterTime + 4 * fee := by
    intro p hg hm
    have htag := caps.groupTag signing p.2 p.1 hm hg
    have hpair1 := sizes.prod_le (rep.ty point₁) (rep.ty message) p
    have hpair2 := sizes.prod_le (rep.ty message) (rep.ty point₁) (p.2, p.1)
    have hfst := localLaws.fst (rep.ty point₁) (rep.ty message) p
    have hsnd := localLaws.snd (rep.ty point₁) (rep.ty message) p
    have hpair := localLaws.pair (QP.snd (rep.ty point₁) (rep.ty message))
      (QP.fst (rep.ty point₁) (rep.ty message)) p
    have hcompose := localLaws.compose
      (QP.pair (QP.snd (rep.ty point₁) (rep.ty message)) (QP.fst (rep.ty point₁) (rep.ty message)))
      (ports.groupTag signing) p
    have hfee : ∀ n ≤ 32 * frameWidth, overhead n ≤ fee := fun _ hn => mono hn
    dsimp only [tagCode] at *
    grind only
  have htag := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing store tagCode
    (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧ Q.size (rep.ty message) p.2 ≤ width)
    (fun r => Q.size bd.idx r ≤ 8 * width) post frameWidth (adapterTime + 4 * fee)
    (by intro p hp; have := sizes.prod_le (rep.ty point₁) (rep.ty message) p; omega) hpost
    (by intro p hp; have h := caps.groupTag signing p.2 p.1 hp.2 hp.1; exact ⟨h.1, h.1.trans hw, ht p hp.1 hp.2⟩)
  intro input hi z hz
  simp only [group, Code.run, sequenceRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨mid, hm, out, ho, rfl⟩ := hz
  obtain ⟨hmid, htime⟩ := hc input hi mid hm
  obtain ⟨hout, htagTime⟩ := htag mid.value ⟨⟨hmid.1.1, hmid.2⟩, hmid.1.2⟩ out ho
  have hin := sizes.prod_le (rep.ty message) store input
  have hm1 := sizes.prod_le (rep.ty point₁) (rep.ty message) mid.value.1
  have hm2 := sizes.prod_le (StepClass.HasProd.prod (rep.ty point₁) (rep.ty message)) store mid.value
  have his := hpre input.2 hi.2
  have him := hi.1
  have hmg := hmid.1.1
  have hmm := hmid.2
  have hms := hpost mid.value.2 hmid.1.2
  have hseq := routing.sequence
    (Q.size (StepClass.HasProd.prod (rep.ty message) store) input)
    (Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod (rep.ty point₁) (rep.ty message)) store) mid.value)
  have hfee := mono (show Q.size (StepClass.HasProd.prod (rep.ty message) store) input +
      Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod (rep.ty point₁) (rep.ty message)) store) mid.value ≤
        32 * frameWidth by dsimp only [pre', post', keep] at *; omega)
  exact ⟨hout, by dsimp only [fee] at *; omega⟩

def handlerTime (overhead : Nat → Nat) (frameWidth replyTime adapterTime dynamicTime : Nat) : Nat :=
  replyTime + dynamicTime + 2 * adapterTime + 40 * overhead (32 * frameWidth)

variable [QO : Q.HasOption] [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  (dispatchLaws : DispatchCostLaws (Q := Q) overhead)

include dispatchLaws

theorem code_bound (pre post : S → Prop) (width frameWidth adapterTime dynamicTime replyTime : Nat)
    (hh : header ≤ width) (hw : 8 * width ≤ frameWidth)
    (hpre : ∀ s, pre s → Q.size store s ≤ frameWidth)
    (hpost : ∀ s, post s → Q.size store s ≤ frameWidth)
    (hpreserve : ∀ s, pre s → post s)
    (caps : PortCaps rep bd ports width adapterTime)
    (samples : DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime)
    (hb : ∀ signing, Bounds control queryCost (reply signing)
      (fun p => Q.size (rep.ty message) p.1 ≤ width ∧ pre p.2)
      (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧ post p.2) replyTime) :
    Bounds control queryCost (code rep bd ports sampler store reply)
      (fun p => RequestSized (Q := Q) rep width p.1 ∧ pre p.2)
      (fun p => Q.size bd.idx p.1 ≤ 8 * width ∧ post p.2)
      (handlerTime overhead frameWidth replyTime adapterTime dynamicTime) := by
  let fee := overhead (32 * frameWidth)
  have hr := random_bound rep bd ports sampler store control queryCost sizes mono routing
    pre post width frameWidth adapterTime dynamicTime hh hw hpre hpreserve caps samples
  have hg := fun signing => group_bound rep bd ports store control queryCost sizes mono routing reply localLaws
    signing pre post width frameWidth adapterTime replyTime hh hw hpre hpost caps (hb signing)
  let preR := fun p : Fin (randomBound + 1) × S => Q.size (rep.ty (boundedNat randomBound)) p.1 ≤ width ∧ pre p.2
  let preG := fun p : M × S => Q.size (rep.ty message) p.1 ≤ width ∧ pre p.2
  let preI := fun p : (Fin (randomBound + 1) ⊕ M) × S =>
    Sum.elim (fun n => preR (n, p.2)) (fun m => preG (m, p.2)) p.1
  let final := fun p : GeneralIndex M G₁ randomBound × S => Q.size bd.idx p.1 ≤ 8 * width ∧ post p.2
  have hi : Bounds control queryCost (inner rep bd ports sampler store reply)
      preI final (max (dynamicTime + adapterTime + 4 * fee) (replyTime + adapterTime + 26 * fee) + 4 * fee) :=
    branchStore_bound_of_width sizes mono control queryCost routing dispatchLaws store
      (random rep bd ports sampler store) (group rep bd ports store reply false)
      preR preG final frameWidth _ _ (by omega)
      (fun p hp => ⟨hp.1.trans (by omega), hpre p.2 hp.2⟩)
      (fun p hp => ⟨hp.1.trans (by omega), hpre p.2 hp.2⟩) hr (hg false)
  have hinnerSize : ∀ p, preI p →
      Q.size (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty message)) p.1 ≤ frameWidth ∧
      Q.size store p.2 ≤ frameWidth := by
    rintro ⟨i, saved⟩ hp
    have hs := sizes.sum_le (rep.ty (boundedNat randomBound)) (rep.ty message) i
    cases i with
    | inl n =>
        have hm := hp.1
        have ht := hpre saved hp.2
        dsimp only [Sum.elim_inl] at hs
        dsimp only at hm ht ⊢
        exact ⟨by omega, ht⟩
    | inr m =>
        have hm := hp.1
        have ht := hpre saved hp.2
        dsimp only [Sum.elim_inr] at hs
        dsimp only at hm ht ⊢
        exact ⟨by omega, ht⟩
  let preO := fun p : GeneralRequest M randomBound × S =>
    Sum.elim (fun i => preI (i, p.2)) (fun m => preG (m, p.2)) p.1
  have ho : Bounds control queryCost (dispatch rep bd ports sampler store reply)
      preO final (max (max (dynamicTime + adapterTime + 4 * fee) (replyTime + adapterTime + 26 * fee) + 4 * fee)
        (replyTime + adapterTime + 26 * fee) + 4 * fee) :=
    branchStore_bound_of_width sizes mono control queryCost routing dispatchLaws store
      (inner rep bd ports sampler store reply) (group rep bd ports store reply true)
      preI preG final frameWidth _ _ (by omega) hinnerSize
      (fun p hp => ⟨hp.1.trans (by omega), hpre p.2 hp.2⟩) hi (hg true)
  have he := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing store ports.request
    (RequestSized (Q := Q) rep width) (RequestSized (Q := Q) rep width) pre frameWidth adapterTime
    (fun i hi => (caps.request i hi).1.trans hw) hpre
    (fun i hi => ⟨hi, (request_size rep sizes width hh i hi).trans (by omega), (caps.request i hi).2⟩)
  have hpreO : ∀ p : GeneralRequest M randomBound × S,
      RequestSized (Q := Q) rep width p.1 ∧ pre p.2 → preO p := by
    rintro ⟨i, saved⟩ hp
    rcases i with (n | m) | m <;> exact hp
  intro input hp z hz
  simp only [code, Code.run, sequenceRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨mid, hm, out, hout, rfl⟩ := hz
  obtain ⟨hmid, heTime⟩ := he input hp mid hm
  obtain ⟨hpost', hoTime⟩ := ho mid.value (hpreO mid.value hmid) out hout
  have hin := sizes.prod_le bd.pos store input
  have hmSize := sizes.prod_le (generalPositions rep randomBound) store mid.value
  have hinPos := (caps.request input.1 hp.1).1
  have hinStore := hpre input.2 hp.2
  have hmPos := request_size rep sizes width hh mid.value.1 hmid.1
  have hmStore := hpre mid.value.2 hmid.2
  have hseq := routing.sequence
    (Q.size (StepClass.HasProd.prod bd.pos store) input)
    (Q.size (StepClass.HasProd.prod (generalPositions rep randomBound) store) mid.value)
  have hfee := mono (show Q.size (StepClass.HasProd.prod bd.pos store) input +
      Q.size (StepClass.HasProd.prod (generalPositions rep randomBound) store) mid.value ≤ 32 * frameWidth by omega)
  exact ⟨hpost', by dsimp only [fee, handlerTime] at *; omega⟩

end Signatures.Runtime.SignatureHandler
