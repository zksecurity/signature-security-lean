import Signatures.Runtime.BackendDispatchBudget

/-! A request-preserving call followed by an implemented reply tagger. The
request and reply predicates may carry length, arity or provenance information;
their entire encodings remain charged while the body executes. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [Q.HasSum]
  {I A B D S : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
  {header : Nat} (sizes : SizeLaws Q header) {overhead : Nat → Nat}
  (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)
  (request : C.Str A) (reply : C.Str B) (index : C.Str D) (store : C.Str S)
  {tag : A × B → D} (tagCode : Q.Realizer (StepClass.HasProd.prod request reply) index tag)
  (body : Code Q spec iface (StepClass.HasProd.prod request store) (StepClass.HasProd.prod reply store))

include sizes laws mono routing

theorem retainedTag_bound_of_width (requestPre : A → Prop) (replyPost : B → Prop)
    (pre post : S → Prop) (width indexWidth tagTime bodyTime : Nat) (hh : header ≤ width) (hw : indexWidth ≤ width)
    (hrequest : ∀ a, requestPre a → Q.size request a ≤ width)
    (hreply : ∀ b, replyPost b → Q.size reply b ≤ width)
    (hpre : ∀ s, pre s → Q.size store s ≤ width)
    (hpost : ∀ s, post s → Q.size store s ≤ width)
    (caps : ∀ a b, requestPre a → replyPost b →
      Q.size index (tag (a, b)) ≤ indexWidth ∧ Q.cost tagCode (a, b) ≤ tagTime)
    (hbody : Bounds control queryCost body (fun p => requestPre p.1 ∧ pre p.2)
      (fun p => replyPost p.1 ∧ post p.2) bodyTime) :
    Bounds control queryCost
      (.seq (Language.withContext store (Q.identity request) body)
        (.first store (.atomic (Q.compose (QP.pair (QP.snd reply request) (QP.fst reply request)) tagCode))))
      (fun p => requestPre p.1 ∧ pre p.2)
      (fun p => Q.size index p.1 ≤ indexWidth ∧ post p.2)
      (bodyTime + tagTime + 26 * overhead (128 * width)) := by
  let fee := overhead (128 * width)
  let pre' := fun p : A × S => requestPre p.1 ∧ pre p.2
  let post' := fun p : B × S => replyPost p.1 ∧ post p.2
  have hc := Language.withContext_bound_of_width sizes laws mono control queryCost routing
    store (Q.identity request) body pre' post' requestPre width fee bodyTime hh
    (by
      intro p hp
      exact ⟨hrequest p.1 hp.1, hpre p.2 hp.2, hrequest p.1 hp.1, hp.1,
        (laws.identity _ _).trans (mono (by have := hrequest p.1 hp.1; omega))⟩)
    (by intro p hp; exact ⟨hreply p.1 hp.1, hpost p.2 hp.2⟩) hbody
  let swappedTag := Q.compose (QP.pair (QP.snd reply request) (QP.fst reply request)) tagCode
  have ht (p : B × A) (hp : replyPost p.1 ∧ requestPre p.2) :
      Q.cost swappedTag p ≤ tagTime + 4 * fee := by
    have htag := caps p.2 p.1 hp.2 hp.1
    have hb := hreply p.1 hp.1
    have ha := hrequest p.2 hp.2
    have hpair1 := sizes.prod_le reply request p
    have hpair2 := sizes.prod_le request reply (p.2, p.1)
    have hfst := laws.fst reply request p
    have hsnd := laws.snd reply request p
    have hpair := laws.pair (QP.snd reply request) (QP.fst reply request) p
    have hcompose := laws.compose (QP.pair (QP.snd reply request) (QP.fst reply request)) tagCode p
    have hfee : ∀ n ≤ 128 * width, overhead n ≤ fee := fun _ hn => mono hn
    dsimp only [swappedTag] at *
    grind only
  have htag := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing store swappedTag
    (fun p => replyPost p.1 ∧ requestPre p.2) (fun r => Q.size index r ≤ indexWidth)
    post (4 * width) (tagTime + 4 * fee)
    (by
      intro p hp
      have := hreply p.1 hp.1
      have := hrequest p.2 hp.2
      exact (sizes.prod_le reply request p).trans (by omega))
    (fun s hs => (hpost s hs).trans (by omega))
    (by intro p hp; exact ⟨(caps p.2 p.1 hp.2 hp.1).1,
      (caps p.2 p.1 hp.2 hp.1).1.trans (by omega), ht p hp⟩)
  intro input hi z hz
  simp only [Code.run, sequenceRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨mid, hm, out, ho, rfl⟩ := hz
  obtain ⟨hmid, htime⟩ := hc input hi mid hm
  obtain ⟨hout, htagTime⟩ := htag mid.value ⟨⟨hmid.1.1, hmid.2⟩, hmid.1.2⟩ out ho
  have hin := sizes.prod_le request store input
  have hm1 := sizes.prod_le reply request mid.value.1
  have hm2 := sizes.prod_le (StepClass.HasProd.prod reply request) store mid.value
  have his := hpre input.2 hi.2
  have hiq := hrequest input.1 hi.1
  have hmr := hreply mid.value.1.1 hmid.1.1
  have hmq := hrequest mid.value.1.2 hmid.2
  have hms := hpost mid.value.2 hmid.1.2
  have hseq := routing.sequence (Q.size (StepClass.HasProd.prod request store) input)
    (Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod reply request) store) mid.value)
  have hfee := mono (show Q.size (StepClass.HasProd.prod request store) input +
      Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod reply request) store) mid.value ≤ 128 * width by omega)
  have hcontextFee := mono (show 32 * width ≤ 128 * width by omega)
  have htagFee := mono (show 32 * (4 * width) ≤ 128 * width by omega)
  exact ⟨hout, by dsimp only [fee] at *; omega⟩

end Signatures.Runtime.BackendProgram
