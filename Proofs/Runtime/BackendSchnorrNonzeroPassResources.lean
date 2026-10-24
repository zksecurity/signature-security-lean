import Proofs.Runtime.BackendSchnorrNonzeroPassTime

/-! Original component resources for one actual nonzero-nonce ROM pass. This record packages
the primitive/profile hypotheses of the proved pass theorem, never a completed
pass, caller, handler or sampler budget. First and replay capacities remain separate. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativePass

open BackendProgram RawTape ListROM ListROM.NativeInterface ListROM.NativeComponents ListROM.NativePass

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [Q.IsDistributive]
  [Q.HasOption] [OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : DataPorts (Q := Q) rep bd) (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  {header : Nat}
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (recovery : ListROM.NativeHandler.RequestRecovery (Q := Q) rep bd) (bound : ExecutionCost)

structure Resources (width tapeWidth managedCap liveCap initialSavedCap remainingCap fuel : Nat) where
  fieldWork : Nat
  fieldVisits : Nat
  fieldQueries : Nat
  nonzeroWork : Nat
  nonzeroVisits : Nat
  nonzeroQueries : Nat
  sourceWidth : Nat
  savedCap : Nat
  counter : Nat
  arityCap : Nat
  tickTime : Nat
  comparisonTime : Nat
  zeroTime : Nat
  natAddTime : Nat
  requestTime : Nat
  responseTime : Nat
  queryTime : Nat
  arityTime : Nat
  replyTime : Nat
  messageTime : Nat
  pointTime : Nat
  scaleTime : Nat
  subTime : Nat
  groupZeroTime : Nat
  scalarAddTime : Nat
  portWidth : Nat
  encodeTime : Nat
  tagTime : Nat
  routeWidth : Nat
  callerTickTime : Nat
  inputTime : Nat
  outputTime : Nat
  optionalTime : Nat
  fieldProfile : ExecutionProfile.Within fieldSampler () fieldWork fieldVisits fieldQueries sourceWidth counter (fun n => n ≤ arityCap)
  nonzeroProfile : ExecutionProfile.Within nonzeroSampler () nonzeroWork nonzeroVisits nonzeroQueries sourceWidth counter (fun n => n ≤ arityCap)
  tick : ∀ n ≤ counter, ∀ size ≤ 6 * NativePrivate.samplerWidth sourceWidth tapeWidth
    (savedCap + 2 * fieldQueries) remainingCap nonzeroQueries, control.loop n size ≤ tickTime
  hh : header ≤ tapeWidth
  hu : Q.size rep.data.unit () ≤ tapeWidth
  hb : ∀ b, Q.size rep.data.bool b ≤ tapeWidth
  hz : Q.size (rep.ty scalar) (0 : F) ≤ tapeWidth
  hn : ∀ n ≤ arityCap + 2, Q.size rep.data.nat n ≤ tapeWidth
  hcompare : ∀ a b, Q.size rep.data.nat a ≤ tapeWidth → Q.size rep.data.nat b ≤ tapeWidth →
    (primitiveBound .natEq).time (a, b) ≤ comparisonTime
  hzero : (primitiveBound .zero).time () ≤ zeroTime
  hnatAdd : ∀ n ≤ arityCap, (primitiveBound .natAdd).time (n, 2) ≤ natAddTime
  hp : ∀ n ≤ arityCap, Q.size iface.position n ≤ tapeWidth
  hr : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.size iface.response ⟨n, r⟩ ≤ tapeWidth
  hrequest : ∀ n ≤ arityCap, Q.cost uniform.request n ≤ requestTime
  hresponse : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.cost uniform.response ⟨n, r⟩ ≤ responseTime
  hquery : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), queryCost n r +
    control.query (Q.size iface.position n) (Q.size iface.response ⟨n, r⟩) ≤ queryTime
  hread : ∀ n ≤ arityCap, Q.cost privatePorts.arity n ≤ arityTime
  hreply : ∀ n ≤ arityCap, ∀ r, Q.size rep.data.nat r ≤ tapeWidth → Q.cost privatePorts.reply (r, n) ≤ replyTime
  hsourceTapeWidth : sourceWidth ≤ tapeWidth
  hstoreWidth : (6 * (savedCap + 2 * fieldQueries + nonzeroQueries + 1 + remainingCap) + 3) * tapeWidth ≤ width
  hm : ∀ x y : M, Q.size (rep.ty message) x ≤ 3 * width → Q.size (rep.ty message) y ≤ 3 * width →
    (primitiveBound .messageEq).time (x, y) ≤ messageTime
  hg : ∀ x y : G₁, Q.size (rep.ty point₁) x ≤ 3 * width → Q.size (rep.ty point₁) y ≤ 3 * width →
    (primitiveBound .point₁Eq).time (x, y) ≤ pointTime
  hscale : ∀ z : F, ∀ g : G₁, Q.size (rep.ty scalar) z ≤ width → Q.size (rep.ty point₁) g ≤ width →
    Q.size (rep.ty point₁) (z • g) ≤ width ∧ (primitiveBound .scale₁).time (z, g) ≤ scaleTime
  hsub : ∀ g pk : G₁, Q.size (rep.ty point₁) g ≤ width → Q.size (rep.ty point₁) pk ≤ width →
    Q.size (rep.ty point₁) (g - pk) ≤ width ∧ (primitiveBound .sub₁).time (g, pk) ≤ subTime
  hgroupZero : Q.size (rep.ty point₁) (0 : G₁) ≤ width
  hgroupZeroTime : (primitiveBound .zero₁).time () ≤ groupZeroTime
  hscalarAdd : ∀ z a : F, Q.size (rep.ty scalar) z ≤ width → Q.size (rep.ty scalar) a ≤ width →
    Q.size (rep.ty scalar) (z + a) ≤ width ∧ (primitiveBound .add).time (z, a) ≤ scalarAddTime
  handlerCaps : ListROM.NativeHandler.PortCaps rep bd ports width tapeWidth arityCap portWidth encodeTime tagTime
  boundaryCaps : PortCaps rep bd boundary width routeWidth bound.peakHeadSize inputTime outputTime optionalTime
  hroute : ListROM.NativeHandler.frameWidth width managedCap liveCap portWidth ≤ routeWidth
  hrequestSize : recovery.recover bound.peakHeadSize ≤ width
  harity : recovery.natural.capacity (recovery.recover bound.peakHeadSize) ≤ arityCap
  hstate : bound.peakStateSize ≤ routeWidth
  hhead : bound.peakHeadSize ≤ routeWidth
  hcallerTick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime
  hmanaged : fuel ≤ managedCap
  hlive : fuel ≤ liveCap
  hsaved : initialSavedCap + fuel * (2 * fieldQueries + nonzeroQueries + 1) ≤ savedCap

variable {width tapeWidth managedCap liveCap initialSavedCap remainingCap fuel : Nat}
  (resources : Resources rep bd boundary ports cost primitive uniform privatePorts fieldSampler nonzeroSampler primitiveBound
    control queryCost recovery bound (header := header) width tapeWidth managedCap liveCap initialSavedCap remainingCap fuel)

variable {rep bd boundary ports cost primitive uniform privatePorts fieldSampler nonzeroSampler primitiveBound control queryCost recovery bound} in
def Resources.timeInputs : TimeInputs where
  fieldWork := resources.fieldWork
  fieldVisits := resources.fieldVisits
  fieldQueries := resources.fieldQueries
  nonzeroWork := resources.nonzeroWork
  nonzeroVisits := resources.nonzeroVisits
  nonzeroQueries := resources.nonzeroQueries
  sourceWidth := resources.sourceWidth
  savedCap := resources.savedCap
  tickTime := resources.tickTime
  comparisonTime := resources.comparisonTime
  zeroTime := resources.zeroTime
  natAddTime := resources.natAddTime
  requestTime := resources.requestTime
  responseTime := resources.responseTime
  queryTime := resources.queryTime
  arityTime := resources.arityTime
  replyTime := resources.replyTime
  messageTime := resources.messageTime
  pointTime := resources.pointTime
  scaleTime := resources.scaleTime
  subTime := resources.subTime
  groupZeroTime := resources.groupZeroTime
  scalarAddTime := resources.scalarAddTime
  portWidth := resources.portWidth
  encodeTime := resources.encodeTime
  tagTime := resources.tagTime
  routeWidth := resources.routeWidth
  callerTickTime := resources.callerTickTime
  inputTime := resources.inputTime
  outputTime := resources.outputTime
  optionalTime := resources.optionalTime

variable {rep bd boundary ports cost primitive uniform privatePorts fieldSampler nonzeroSampler primitiveBound control queryCost recovery bound} in
def Resources.time (overhead : Nat → Nat) : Nat :=
  resources.timeInputs.time overhead bound width tapeWidth managedCap liveCap remainingCap fuel

include resources in
omit [Q.HasCategory] QP QS [Q.IsDistributive] [Q.HasOption] [OptionCode (Q := Q)] in
theorem Resources.tapeWidth_le : tapeWidth ≤ width := by
  have h := resources.hstoreWidth
  nlinarith only [h, Nat.zero_le ((resources.savedCap + 2 * resources.fieldQueries + resources.nonzeroQueries + 1 + remainingCap) * tapeWidth)]

variable (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead) (mono : Monotone overhead)
  (routing : RoutingCostLaws control overhead) (dispatch : DispatchCostLaws (Q := Q) overhead)

include sizes mono routing in
omit [Q.HasCategory] QP QS [Q.IsDistributive] [Q.HasOption] [OptionCode (Q := Q)] in
theorem Resources.fieldSampler_bound :
    Bounds control queryCost fieldSampler (fun _ => True) (fun f => Q.size (rep.ty scalar) f ≤ tapeWidth)
      (ExecutionProfile.runtimeBound overhead tapeWidth resources.fieldWork resources.fieldVisits resources.fieldQueries
        resources.tickTime resources.queryTime) := by
  have tick : ∀ n ≤ resources.counter, ∀ size ≤ 3 * tapeWidth, control.loop n size ≤ resources.tickTime := by
    intro n hn size hs
    apply resources.tick n hn size
    unfold NativePrivate.samplerWidth NativePrivate.frameWidth
    nlinarith
  have profile : ∀ input : Unit, True → ExecutionProfile.Within fieldSampler input resources.fieldWork resources.fieldVisits
      resources.fieldQueries tapeWidth resources.counter (fun n => n ≤ resources.arityCap) := by
    intro input _ r hr
    cases input
    obtain ⟨hw, hv, hq, hf⟩ := resources.fieldProfile r hr
    exact ⟨hw, hv, hq, hf.1.trans resources.hsourceTapeWidth, hf.2⟩
  exact ExecutionProfile.within_bound control queryCost sizes tapeWidth resources.counter
    (fun n => n ≤ resources.arityCap) resources.hh mono routing resources.tickTime resources.queryTime tick
    resources.hquery fieldSampler (fun _ => True) resources.fieldWork resources.fieldVisits resources.fieldQueries profile

variable [SampleableType F] [SampleableType Fˣ] (fieldLaw : fieldSampler.denote () = ($ᵗ F : ProbComp F))
  (nonzeroLaw : nonzeroSampler.denote () = (fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd)) (hrun : R.RunsWithin (fun _ => bound))

include fieldLaw nonzeroLaw sizes lists laws dataLaws mono routing dispatch hrun in
theorem Resources.pass_bound :
    Bounds control queryCost (code rep bd boundary data cost primitive fieldSampler nonzeroSampler ports uniform privatePorts R fuel)
      (fun p => ConfigBound (Q := Q) rep width p.2 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth initialSavedCap remainingCap p.1)
      (ResultBound (Q := Q) rep width tapeWidth managedCap (liveCap + 1) (resources.savedCap + 1) remainingCap)
      (resources.time overhead) := by
  exact code_bound_of_resources rep bd boundary ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler fieldLaw nonzeroLaw
    sizes lists laws dataLaws primitiveBound mono control queryCost routing dispatch R recovery bound hrun
    resources.fieldWork resources.fieldVisits resources.fieldQueries resources.nonzeroWork resources.nonzeroVisits resources.nonzeroQueries resources.sourceWidth tapeWidth resources.savedCap remainingCap
    resources.counter resources.arityCap resources.tickTime resources.comparisonTime resources.zeroTime resources.natAddTime
    resources.requestTime resources.responseTime resources.queryTime resources.arityTime resources.replyTime
    width managedCap liveCap resources.messageTime resources.pointTime resources.scaleTime resources.subTime resources.groupZeroTime resources.scalarAddTime
    resources.fieldProfile resources.nonzeroProfile resources.tick resources.hh resources.hu resources.hb resources.hz resources.hn resources.hcompare
    resources.hzero resources.hnatAdd resources.hp resources.hr resources.hrequest resources.hresponse resources.hquery
    resources.hread resources.hreply resources.hsourceTapeWidth resources.hstoreWidth resources.hm resources.hg
    resources.hscale resources.hsub resources.hgroupZero resources.hgroupZeroTime resources.hscalarAdd resources.portWidth resources.encodeTime resources.tagTime resources.routeWidth fuel
    resources.callerTickTime initialSavedCap resources.inputTime resources.outputTime resources.optionalTime
    resources.handlerCaps resources.boundaryCaps resources.hroute resources.hrequestSize resources.harity resources.hstate
    resources.hhead resources.hcallerTick resources.hmanaged resources.hlive resources.hsaved

end Signatures.Runtime.Schnorr.NonzeroListROM.NativePass
