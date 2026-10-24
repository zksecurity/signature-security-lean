import Proofs.Runtime.BackendSchnorrAGMSolverSetup
import Proofs.Runtime.BackendSchnorrAGMSolverTerminalBudget

/-! Whole native Schnorr AGM runtime from the general attacker's measured
resources. Setup, adaptive caller execution, output inspection and extraction
are composed with their actual control charges. No whole-solver budget is an
assumption, and the bound includes runs that exhaust the supplied query fuel. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Solver

open BackendProgram Interface

def programWidth (inputWidth width outputWidth routeWidth cap basisCap signedCap : Nat) : Nat :=
  4 * (inputWidth + routeWidth + terminalWidth width outputWidth routeWidth cap basisCap signedCap)

def programTime (overhead : Nat → Nat) (bound : ExecutionCost)
    (inputWidth width outputWidth routeWidth cap basisCap signedCap groupCap rowCap coeffCap portWidth
      fuel tickTime adapterTime divisionTime : Nat) (t : Handler.Times) : Nat :=
  setupTime overhead inputWidth width routeWidth t.fieldTime adapterTime +
    Handler.callerTime overhead routeWidth fuel (bound.work + 2 * bound.queries + 2)
      (fun _ => bound.queries) (Handler.timeBudget overhead width cap basisCap signedCap groupCap rowCap coeffCap portWidth t) tickTime +
    terminalTime overhead width outputWidth routeWidth cap basisCap signedCap adapterTime
      t.comparisonTime t.subtractTime t.incrementTime t.messageTime t.pointTime t.fieldTime t.mulTime t.equalityTime
      t.sampleTime divisionTime t.pointZeroTime +
    2 * overhead (32 * programWidth inputWidth width outputWidth routeWidth cap basisCap signedCap)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [Q.HasOption]
  [QD : Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [DecidableEq (SourceRequest F G₁ M)]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor (SourceInput G₁) (SourceForgery F G₁ M))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (ports : Ports (Q := Q) rep bd)
  (randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (lengths : ListLengthLaws Q rep.data) (payloads : ListPayloadLaws Q rep.data)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead) (dispatch : DispatchCostLaws (Q := Q) overhead)
  (recovery : Handler.RequestRecovery (Q := Q) rep bd)
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))

include sizes lists lengths payloads laws dataLaws primitiveBound mono routing dispatch recovery hrun

theorem program_bound
    (inputWidth width outputWidth routeWidth cap basisCap signedCap groupCap rowCap coeffCap arityCap portWidth
      fuel tickTime adapterTime divisionTime : Nat) (t : Handler.Times)
    (hh : header ≤ width) (hc : fuel ≤ cap) (hn : fuel + 2 ≤ basisCap) (hs : fuel ≤ signedCap)
    (hroute : Handler.frameWidth width cap basisCap signedCap groupCap rowCap coeffCap portWidth ≤ routeWidth)
    (handlerCaps : Handler.PortCaps rep bd ports width groupCap rowCap coeffCap arityCap portWidth t.requestTime t.tagTime)
    (solverCaps : PortCaps rep bd boundary width outputWidth routeWidth adapterTime)
    (primitives : Handler.PrimitiveCaps rep cost primitive randomPorts sampler control queryCost primitiveBound width basisCap arityCap t)
    (hrequest : recovery.recover bound.peakHeadSize ≤ width)
    (hgroups : recovery.recover bound.peakHeadSize ≤ groupCap)
    (hrows : recovery.recover bound.peakHeadSize ≤ rowCap)
    (hcoeff : recovery.recover bound.peakHeadSize ≤ coeffCap)
    (harity : recovery.natural.capacity (recovery.recover bound.peakHeadSize) ≤ arityCap)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (htick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime)
    (hone : (primitiveBound .one).time () ≤ t.fieldTime)
    (hm : ∀ a b : M, Q.size (rep.ty message) a ≤ 15 * max width outputWidth →
      Q.size (rep.ty message) b ≤ 15 * max width outputWidth → (primitiveBound .messageEq).time (a, b) ≤ t.messageTime)
    (hg : ∀ a b : G₁, Q.size (rep.ty point₁) a ≤ 15 * max width outputWidth →
      Q.size (rep.ty point₁) b ≤ 15 * max width outputWidth → (primitiveBound .point₁Eq).time (a, b) ≤ t.pointTime)
    (hsub : ∀ a b : F, (primitiveBound .sub).time (a, b) ≤ t.fieldTime)
    (hdiv : ∀ a b : F, (primitiveBound .div).time (a, b) ≤ divisionTime) :
    Bounds control queryCost (program rep bd boundary data cost primitive ports randomPorts sampler R fuel)
      (fun input => Q.size (rep.env inputTypes) input ≤ inputWidth)
      (fun out => Q.size (rep.ty scalar) out ≤ terminalWidth width outputWidth routeWidth cap basisCap signedCap)
      (programTime overhead bound inputWidth width outputWidth routeWidth cap basisCap signedCap
        groupCap rowCap coeffCap portWidth fuel tickTime adapterTime divisionTime t) := by
  let W := terminalWidth width outputWidth routeWidth cap basisCap signedCap
  let B := programWidth inputWidth width outputWidth routeWidth cap basisCap signedCap
  let pre := fun input => Q.size (rep.env inputTypes) input ≤ inputWidth
  let started := fun p : SourceInput G₁ × ((G₁ × G₁) × EncodedState F G₁ M) =>
    Handler.ReservedState (Q := Q) rep width cap basisCap signedCap fuel p.2 ∧ Q.size bd.input p.1 ≤ routeWidth
  let returned := fun p : Option (SourceForgery F G₁ M) × ((G₁ × G₁) × EncodedState F G₁ M) =>
    ResultReady (Q := Q) bd routeWidth p.1 ∧ HandlerComponents.StoreBound (Q := Q) rep width cap basisCap signedCap p.2
  let post := fun out : F => Q.size (rep.ty scalar) out ≤ W
  have hw : width ≤ W := by dsimp only [W, terminalWidth]; omega
  have hr : routeWidth ≤ W := by dsimp only [W, terminalWidth]; omega
  have hstore (saved) (h : HandlerComponents.StoreBound (Q := Q) rep width cap basisCap signedCap saved) :
      Q.size (rep.ty storeTy) saved ≤ W :=
    (HandlerComponents.store_size rep sizes lists width cap basisCap signedCap hh primitives.bool primitives.scalar saved h).trans
      (by dsimp only [W, terminalWidth]; omega)
  have hiSize (input) (hi : pre input) : Q.size (rep.env inputTypes) input ≤ B :=
    hi.trans (by dsimp only [B, programWidth]; omega)
  have hsSize (p) (hp : started p) : Q.size (StepClass.HasProd.prod bd.input (rep.ty storeTy)) p ≤ B := by
    have hprod := sizes.prod_le bd.input (rep.ty storeTy) p
    have hi := hp.2
    have hs := hstore p.2 hp.1.store
    dsimp only [B, programWidth]
    change _ ≤ 4 * (inputWidth + routeWidth + W)
    omega
  have hrSize (p) (hp : returned p) : Q.size (Caller.result (bd := bd) (rep.ty storeTy)) p ≤ B := by
    have hs := hstore p.2 hp.2
    have ho : Q.size (StepClass.HasOption.option bd.out) p.1 ≤ routeWidth + width := by
      cases hopt : p.1 with
      | none => exact (sizes.none_le bd.out).trans (by omega)
      | some out =>
          have hout := hp.1 out hopt
          exact (sizes.some_le bd.out out).trans (by omega)
    have hprod := sizes.prod_le (StepClass.HasOption.option bd.out) (rep.ty storeTy) p
    change Q.size (StepClass.HasProd.prod (StepClass.HasOption.option bd.out) (rep.ty storeTy)) p ≤ _
    dsimp only [B, programWidth]
    change _ ≤ 4 * (inputWidth + routeWidth + W)
    omega
  have hsetup := setup_bound (iface := iface) rep bd boundary data cost primitive sizes lists laws dataLaws primitiveBound mono
    control queryCost routing inputWidth width routeWidth cap basisCap signedCap fuel t.fieldTime adapterTime
    hh primitives.unit primitives.bool primitives.scalar primitives.point hc hn hs primitives.zero hone solverCaps.input
  have hcaller : Bounds control queryCost (Handler.caller rep bd ports data cost primitive randomPorts sampler R fuel)
      started returned (Handler.callerTime overhead routeWidth fuel (bound.work + 2 * bound.queries + 2)
        (fun _ => bound.queries) (Handler.timeBudget overhead width cap basisCap signedCap groupCap rowCap coeffCap portWidth t) tickTime) := by
    intro input hi z hz
    obtain ⟨hout, ht⟩ := Handler.caller_bound_of_resources rep bd sizes R recovery bound hrun ports data cost primitive randomPorts sampler
      control queryCost primitiveBound lists laws dataLaws mono routing dispatch
      width cap basisCap signedCap groupCap rowCap coeffCap arityCap portWidth routeWidth fuel tickTime t hh hroute handlerCaps primitives
      hrequest hgroups hrows hcoeff harity hstate hhead htick input.1 input.2 hi.1 hi.2 z hz
    refine ⟨⟨?_, hout.store⟩, ht⟩
    intro out ho
    exact (Handler.caller_output_size_of_resources rep bd ports data cost primitive randomPorts sampler control queryCost R bound hrun
      sizes fuel input.1 input.2 z hz out ho).trans hhead
  have hsample : Bounds control queryCost sampler (fun _ => True)
      (fun c => Q.size (rep.ty scalar) c ≤ max width outputWidth) t.sampleTime := by
    intro input hi z hz
    obtain ⟨hout, ht⟩ := primitives.sample input hi z hz
    exact ⟨hout.trans (le_max_left _ _), ht⟩
  have hterminal := terminal_bound rep bd boundary data cost primitive sampler sizes lists lengths payloads laws dataLaws primitiveBound mono
    control queryCost routing dispatch width outputWidth routeWidth cap basisCap signedCap adapterTime
    t.comparisonTime t.subtractTime t.incrementTime t.messageTime t.pointTime t.fieldTime t.mulTime t.equalityTime t.sampleTime divisionTime t.pointZeroTime
    hh primitives.unit primitives.bool primitives.scalar solverCaps
    (fun n hn => (primitives.natural n (hn.trans (Nat.le_max_left _ _))).trans (le_max_left _ _))
    primitives.comparison primitives.subtract primitives.increment hm hg primitives.zero primitives.add primitives.mul primitives.scalarEq
    hsample hsub hdiv ((primitives.point 0).trans (le_max_left _ _)) primitives.pointZero
  have htail := seq_bound_of_width mono control queryCost routing _ _ started returned post B _ _ hsSize hrSize hcaller hterminal
  have hall := seq_bound_of_width mono control queryCost routing _ _ pre started post B _ _ hiSize hsSize hsetup htail
  intro input hi z hz
  obtain ⟨hout, ht⟩ := hall input hi z hz
  exact ⟨hout, by dsimp only [programTime, B] at *; omega⟩

end Signatures.Runtime.SchnorrAGM.Native.Solver
