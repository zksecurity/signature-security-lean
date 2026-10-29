import Proofs.Runtime.GeneralSyncWrapUpdateCost6
import Proofs.Runtime.GeneralCallerResources
import Proofs.Runtime.BackendWeightedCallerResources
import PolyFun.Realizability.Quantitative.TraceCost

/-! # The wrapper runs within a derived budget

Every reachable wrapper state holds a reachable attacker state, so the attacker's own execution
contract bounds the inner costs and sizes; each wrapper step adds one readout and one transition
within the budgets of the previous files. A trace of the wrapper makes at most one query per
attacker query, per signing request and once more for the final hash, so the whole run stays
within one explicit record. -/

open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation
open PFunctor.DynSystem.DynComputation.RankedResource
open Signatures.Runtime.WeightedAGM (GeneralRequest GeneralIndex BoundedRandomReply generalSpec
  generalPositions NativePorts tagRandom tagHash tagSign)
open Signatures.Runtime.BackendProgram
open Signatures.Runtime.BackendProgram.FrameCost (fee)

namespace Signatures.Runtime.SyncWrapGeneral

set_option linter.unusedSectionVars false

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {randomBound : Nat}
  {rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M)}
  {data : DataCode Q rep.data} {cost : PrimitiveCosts}
  {primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr)}
  {bdI : Boundary C (generalSpec (key.Value (cryptoBase F G₁ G₂ K M))
    (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor (G₂ × G₂)
    (OutTy.Value (cryptoBase F G₁ G₂ K M))}
  {ports : NativePorts (Q := Q) rep key Weights.syncMessage bdI}
  {wports : WrapPorts rep ports}
  {correction finalFn : K × F → F} {keys : G₂ → G₂ × G₂}
  {code : SchemeCode (Q := Q) rep correction finalFn keys}
  {R : GeneralCaller.Caller (Q := Q) (bd := bdI)}
  {overhead : Nat → Nat}
  {primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr)}
  {header : Nat}
  {width cap routeWidth outputWidth finishedRoute : Nat}
  {adapterTime routineTime opTime comparisonTime : Nat}
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
  (recovery : WeightedAGM.NativeHandler.RequestRecovery (Q := Q) rep key Weights.syncMessage bdI)
  (hrec : recovery.recover bound.peakHeadSize ≤ width)
  (S : Caps rep data cost primitive ports wports correction finalFn keys code primitiveBound overhead header
    width cap bound.peakStateSize bound.peakHeadSize routeWidth outputWidth finishedRoute adapterTime routineTime opTime
    comparisonTime)

attribute [local implicit_reducible] PFunctor.Idx

local notation "prod" => StepClass.HasProd.prod
local notation "sum" => StepClass.HasSum.sum
local notation "W" => caller rep data cost primitive ports wports correction finalFn keys code R

/-! ## The attacker's own contract at reachable states -/

include hrun S recovery hrec

/-- A reachable attacker state satisfies the wrapper's inner contract. -/
theorem innerState_of_reachable (s : R.machine.State) (hs : GeneralCaller.Reachable R s) :
    InnerState rep width bound.peakStateSize bound.peakHeadSize bound.work s := by
  obtain ⟨hstate, hhead⟩ := GeneralCaller.reachable_sizes R bound hrun s hs
  refine ⟨hstate, hhead, ?_, ?_⟩
  · obtain ⟨input, ⟨trace⟩⟩ := hs
    have hc := (hrun.cost_le input trace).1
    rw [executionCost_eq_init_add_trace_add_terminal] at hc
    simp only [ExecutionCost.work_add, ExecutionCost.work_ofWork, terminalCost, ExecutionCost.work_observe] at hc
    omega
  · intro i next hv
    have hr := WeightedAGM.NativeHandler.reachable_request rep key Weights.syncMessage bdI S.sizes R recovery bound hrun s hs
      i next hv
    rcases i with (n | t) | m <;> exact hr.trans hrec

omit S recovery hrec in
/-- An enabled transition of a reachable attacker state is within its work budget. -/
theorem innerUpdate_of_reachable (s : R.machine.State) (hs : GeneralCaller.Reachable R s)
    (i : GeneralRequest K (K × F) randomBound) (next : (generalSpec K (K × F) G₁ randomBound).Range i → R.machine.State)
    (hv : R.machine.view s = .inr ⟨i, next⟩) (dir : (generalSpec K (K × F) G₁ randomBound).Range i) :
    Q.cost R.updateCode (s, ⟨i, dir⟩) ≤ bound.work := by
  obtain ⟨input, ⟨trace⟩⟩ := hs
  have hc := (hrun.cost_le input (trace.append (.query hv dir (.nil _)))).1
  rw [executionCost_eq_init_add_trace_add_terminal] at hc
  simp only [ExecutionCost.work_add, ExecutionCost.work_ofWork, terminalCost, ExecutionCost.work_observe,
    QuantitativeRealization.ExecutionTrace.cost_append, executionTrace_cost_query, queryStepCost,
    QuantitativeRealization.ExecutionTrace.cost, ExecutionCost.work_query, Nat.add_zero] at hc
  omega

omit S recovery hrec in
/-- Initialization of the attacker is within its work budget. -/
theorem innerInit_cost (input : G₂ × G₂) :
    Q.cost R.initCode input ≤ bound.work := by
  have hc := (hrun.cost_le input (.nil _)).1
  rw [executionCost_eq_init_add_trace_add_terminal] at hc
  simp only [ExecutionCost.work_add, ExecutionCost.work_ofWork, terminalCost, ExecutionCost.work_observe,
    QuantitativeRealization.ExecutionTrace.cost, ExecutionCost.work_zero] at hc
  omega

/-! ## The wrapper's reachable states -/

omit hrun S recovery hrec in
variable (R) in
/-- Wrapper states linked to reachable attacker states, with at most `k` marks. -/
def Linked (k : Nat) : State R.machine (F := F) → Prop
  | .inl (s, marks) => GeneralCaller.Reachable R s ∧ marks.length ≤ k
  | .inr (.inl (s, _, marks)) => GeneralCaller.Reachable R s ∧ marks.length ≤ k ∧
      ∃ m next, R.machine.view s = .inr ⟨.inr m, next⟩
  | .inr (.inr (result, marks)) => (∃ s, GeneralCaller.Reachable R s ∧ R.machine.view s = .inl result) ∧ marks.length ≤ k

theorem wrapState_of_linked (k : Nat) (hk : k ≤ cap) (st : State R.machine (F := F)) (hst : Linked R k st) :
    WrapState rep width cap bound.peakStateSize bound.peakHeadSize bound.work st := by
  rcases st with ⟨s, marks⟩ | ⟨s, h, marks⟩ | ⟨result, marks⟩
  · exact .ready (innerState_of_reachable bound hrun recovery hrec S s hst.1) (by have := hst.2; omega)
  · exact .gotHash (innerState_of_reachable bound hrun recovery hrec S s hst.1) (by have := hst.2.1; omega)
  · obtain ⟨⟨s, hs, hv⟩, hl⟩ := hst
    exact .done ((innerState_of_reachable bound hrun recovery hrec S s hs).output S result hv) (by omega)

/-- The wrapper's exposed position at a linked ready or waiting state is a sized request, and
its tagged replies are sized. -/
theorem linked_step_sizes (k : Nat) (hk : k ≤ cap) (st : State R.machine (F := F)) (hst : Linked R k st)
    (position : GeneralRequest K (K × F) randomBound)
    (next' : (generalSpec K (K × F) G₁ randomBound).Range position → State R.machine (F := F))
    (hview : (wrapped correction finalFn keys R).view st = .inr ⟨position, next'⟩)
    (dir : (generalSpec K (K × F) G₁ randomBound).Range position) :
    Q.size bdI.pos position ≤ 8 * width ∧ Q.size bdI.idx ⟨position, dir⟩ ≤ 8 * width := by
  have hh := S.fcaps.hdr
  rcases st with ⟨s, marks⟩ | ⟨s, h, marks⟩ | ⟨result, marks⟩
  · have hs := innerState_of_reachable bound hrun recovery hrec S s hst.1
    rw [view_ofStep, step_ready] at hview
    rcases hv : R.machine.view s with result | ⟨(n | t) | m, next⟩
    · rw [readyStep_inl R.machine finalIndex hv] at hview
      obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp (Sum.inr.inj hview)
      obtain ⟨hdec, -⟩ := S.wcaps.output result ((hs.output S result hv).trans S.headRoute)
      have hkey := outputKey_size S result hdec
      exact ⟨(hashPos_size S _ hkey).2, (S.pcaps.hashTag _ dir hkey (S.point₁ dir)).1⟩
    · rw [readyStep_random R.machine finalIndex hv] at hview
      obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp (Sum.inr.inj hview)
      exact ⟨(S.pcaps.request _ (hs.request _ next hv)).1, (S.pcaps.randomTag ⟨n, dir⟩).1⟩
    · rw [readyStep_hash R.machine finalIndex hv] at hview
      obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp (Sum.inr.inj hview)
      have hreq := hs.request _ next hv
      exact ⟨(S.pcaps.request _ hreq).1, (S.pcaps.hashTag t dir hreq (S.point₁ dir)).1⟩
    · rw [readyStep_sign R.machine finalIndex hv] at hview
      obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp (Sum.inr.inj hview)
      have hreq := hs.request _ next hv
      have hkey : Q.size (rep.ty key) m.1 ≤ width := (S.sizes.fst_le _ _ m).trans hreq
      exact ⟨(hashPos_size S _ hkey).2, (S.pcaps.hashTag m.1 dir hkey (S.point₁ dir)).1⟩
  · have hs := innerState_of_reachable bound hrun recovery hrec S s hst.1
    obtain ⟨-, -, m, next, hv⟩ := hst
    rw [view_ofStep, step_gotHash R.machine correction finalIndex (fin finalFn) hv] at hview
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp (Sum.inr.inj hview)
    have hreq := hs.request _ next hv
    exact ⟨(S.pcaps.request _ hreq).1, (S.pcaps.signTag m dir hreq (S.point₁ dir)).1⟩
  · rw [view_ofStep, step_done] at hview
    exact absurd hview (by simp)

/-- One enabled step of the wrapper: the transition is within budget and the next state is linked
with at most one more mark. -/
theorem linked_step (k : Nat) (hk : k + 1 ≤ cap) (st : State R.machine (F := F)) (hst : Linked R k st)
    (position : GeneralRequest K (K × F) randomBound)
    (next' : (generalSpec K (K × F) G₁ randomBound).Range position → State R.machine (F := F))
    (hview : (wrapped correction finalFn keys R).view st = .inr ⟨position, next'⟩)
    (dir : (generalSpec K (K × F) G₁ randomBound).Range position) :
    Q.cost (updateCode rep data cost primitive ports wports correction finalFn keys code R) (st, ⟨position, dir⟩) ≤
      updateTime overhead width cap bound.peakStateSize routeWidth outputWidth finishedRoute adapterTime routineTime opTime
        comparisonTime bound.work ∧
    Linked R (k + 1) (next' dir) := by
  rcases st with ⟨s, marks⟩ | ⟨s, h, marks⟩ | ⟨result, marks⟩
  · have hs := innerState_of_reachable bound hrun recovery hrec S s hst.1
    have hreach := hst.1
    have hml : marks.length ≤ cap := by have := hst.2; omega
    rw [view_ofStep, step_ready] at hview
    rcases hv : R.machine.view s with result | ⟨(n | t) | m, next⟩
    · rw [readyStep_inl R.machine finalIndex hv] at hview
      obtain ⟨rfl, hnext⟩ := Sigma.mk.inj_iff.mp (Sum.inr.inj hview)
      rw [← eq_of_heq hnext]
      refine ⟨updateCode_cost S _ _ (Or.inl ⟨s, marks, rfl, hs, hml, Or.inl ⟨result, dir, hv, rfl⟩⟩), ?_⟩
      exact ⟨⟨s, hreach, hv⟩, by have := hst.2; omega⟩
    · rw [readyStep_random R.machine finalIndex hv] at hview
      obtain ⟨rfl, hnext⟩ := Sigma.mk.inj_iff.mp (Sum.inr.inj hview)
      rw [← eq_of_heq hnext]
      have hreach' := GeneralCaller.reachable_step R s hreach _ next hv dir
      refine ⟨updateCode_cost S _ _ (Or.inl ⟨s, marks, rfl, hs, hml, Or.inr (Or.inl ⟨_, next, dir, hv, rfl, rfl,
        innerUpdate_of_reachable bound hrun s hreach _ next hv dir,
        (GeneralCaller.reachable_sizes R bound hrun _ hreach').1⟩)⟩), ?_⟩
      exact ⟨hreach', by have := hst.2; omega⟩
    · rw [readyStep_hash R.machine finalIndex hv] at hview
      obtain ⟨rfl, hnext⟩ := Sigma.mk.inj_iff.mp (Sum.inr.inj hview)
      rw [← eq_of_heq hnext]
      have hreach' := GeneralCaller.reachable_step R s hreach _ next hv dir
      refine ⟨updateCode_cost S _ _ (Or.inl ⟨s, marks, rfl, hs, hml, Or.inr (Or.inl ⟨_, next, dir, hv, rfl, rfl,
        innerUpdate_of_reachable bound hrun s hreach _ next hv dir,
        (GeneralCaller.reachable_sizes R bound hrun _ hreach').1⟩)⟩), ?_⟩
      exact ⟨hreach', by have := hst.2; simp; omega⟩
    · rw [readyStep_sign R.machine finalIndex hv] at hview
      obtain ⟨rfl, hnext⟩ := Sigma.mk.inj_iff.mp (Sum.inr.inj hview)
      rw [← eq_of_heq hnext]
      refine ⟨updateCode_cost S _ _ (Or.inl ⟨s, marks, rfl, hs, hml, Or.inr (Or.inr ⟨m, next, dir, hv, rfl⟩)⟩), ?_⟩
      exact ⟨hreach, by have := hst.2; omega, m, next, hv⟩
  · have hs := innerState_of_reachable bound hrun recovery hrec S s hst.1
    obtain ⟨hreach, hl, m, next, hv⟩ := hst
    have hml : marks.length ≤ cap := by omega
    rw [view_ofStep, step_gotHash R.machine correction finalIndex (fin finalFn) hv] at hview
    obtain ⟨rfl, hnext⟩ := Sigma.mk.inj_iff.mp (Sum.inr.inj hview)
    rw [← eq_of_heq hnext]
    have hreach' := GeneralCaller.reachable_step R s hreach _ next hv (dir + correction m • h)
    refine ⟨updateCode_cost S _ _ (Or.inr ⟨s, h, marks, m, next, dir, rfl, hs, hml, hv, rfl,
      innerUpdate_of_reachable bound hrun s hreach _ next hv _, (GeneralCaller.reachable_sizes R bound hrun _ hreach').1⟩), ?_⟩
    exact ⟨hreach', by simp; omega⟩
  · rw [view_ofStep, step_done] at hview
    exact absurd hview (by simp)


/-! ## Sizes of linked states -/

/-- A linked state is within the wrapper's state width. -/
theorem linked_state_size (k : Nat) (hk : k ≤ cap) (st : State R.machine (F := F)) (hst : Linked R k st) :
    Q.size (stateRep rep R) st ≤ stateWidth width cap bound.peakStateSize routeWidth := by
  have hh := S.fcaps.hdr
  have hmarks : ∀ marks : List (Mark F), marks.length ≤ k → Q.size (marksRep rep) marks ≤ marksWidth width cap :=
    fun marks hl => marks_size rep S.sizes S.lists width cap hh S.fcaps.bool S.fcaps.scalar marks (by omega)
  refine state_size rep S.sizes R width cap bound.peakStateSize routeWidth hh S.point₁ st ?_ ?_ ?_ ?_
  · rintro s marks rfl
    exact (GeneralCaller.reachable_sizes R bound hrun s hst.1).1
  · rintro s h marks rfl
    exact (GeneralCaller.reachable_sizes R bound hrun s hst.1).1
  · rintro result marks rfl
    obtain ⟨⟨s, hs, hv⟩, -⟩ := hst
    exact ((innerState_of_reachable bound hrun recovery hrec S s hs).output S result hv).trans S.headRoute
  · intro marks hcase
    rcases st with ⟨s, marks'⟩ | ⟨s, h, marks'⟩ | ⟨result, marks'⟩
    · rcases hcase with ⟨s', hs'⟩ | ⟨s', h', hs'⟩ | ⟨result', hs'⟩
      · cases hs'; exact hmarks marks hst.2
      · exact absurd hs' (by simp [gotHash, ready])
      · exact absurd hs' (by simp [done, ready])
    · rcases hcase with ⟨s', hs'⟩ | ⟨s', h', hs'⟩ | ⟨result', hs'⟩
      · exact absurd hs' (by simp [gotHash, ready])
      · cases hs'; exact hmarks marks hst.2.1
      · exact absurd hs' (by simp [done, gotHash])
    · rcases hcase with ⟨s', hs'⟩ | ⟨s', h', hs'⟩ | ⟨result', hs'⟩
      · exact absurd hs' (by simp [done, ready])
      · exact absurd hs' (by simp [done, gotHash])
      · cases hs'; exact hmarks marks hst.2

/-! ## The whole run -/

omit hrun S recovery hrec in
/-- The wrapper's execution budget: initialization, one readout per visited state, one
transition and one query's traffic per step, the state and readout widths. -/
def wrapExecution (overhead : Nat → Nat) (width cap innerWidth routeWidth outputWidth finishedRoute adapterTime routineTime
    opTime comparisonTime work : Nat) : ExecutionCost where
  work := initTime overhead width cap innerWidth routeWidth outputWidth finishedRoute adapterTime routineTime work +
    (cap + 1) * headTime overhead width cap innerWidth routeWidth outputWidth finishedRoute adapterTime routineTime opTime work +
    cap * updateTime overhead width cap innerWidth routeWidth outputWidth finishedRoute adapterTime routineTime opTime
      comparisonTime work
  queries := cap
  traffic := cap * (16 * width)
  peakStateSize := stateWidth width cap innerWidth routeWidth
  peakHeadSize := 9 * width + finishedRoute

local notation "HT" => headTime overhead width cap bound.peakStateSize routeWidth outputWidth finishedRoute adapterTime
  routineTime opTime bound.work
local notation "UT" => updateTime overhead width cap bound.peakStateSize routeWidth outputWidth finishedRoute adapterTime
  routineTime opTime comparisonTime bound.work
local notation "SW" => stateWidth width cap bound.peakStateSize routeWidth

/-- Along a trace from a linked state, every component of the cost is bounded step by step, and the
final state is linked with one more mark per step. -/
theorem trace_bound (k : Nat) {st finish : (W).machine.State} (hst : Linked R k st)
    (trace : (W).ExecutionTrace st finish) (hk : k + trace.length ≤ cap) :
    trace.cost.work ≤ trace.length * (HT + UT) ∧ trace.cost.traffic ≤ trace.length * (16 * width) ∧
    trace.cost.peakStateSize ≤ SW ∧ trace.cost.peakHeadSize ≤ 9 * width + finishedRoute ∧
    Linked R (k + trace.length) finish := by
  induction trace generalizing k with
  | nil state =>
    simp only [QuantitativeRealization.ExecutionTrace.cost, QuantitativeRealization.ExecutionTrace.length,
      ExecutionCost.work_zero, ExecutionCost.traffic_zero, ExecutionCost.peakStateSize_zero, ExecutionCost.peakHeadSize_zero,
      Nat.zero_mul, Nat.add_zero]
    exact ⟨le_rfl, le_rfl, Nat.zero_le _, Nat.zero_le _, hst⟩
  | @query state position next finish view_eq direction tail ih =>
    simp only [QuantitativeRealization.ExecutionTrace.length] at hk ⊢
    have hk1 : k + 1 ≤ cap := by omega
    obtain ⟨tupd, hlinked⟩ := linked_step bound hrun recovery hrec S k hk1 state hst position next view_eq direction
    obtain ⟨hpos, hidx⟩ := linked_step_sizes bound hrun recovery hrec S k (by omega) state hst position next view_eq direction
    obtain ⟨thead, hhead⟩ := headCode_cost S state (wrapState_of_linked bound hrun recovery hrec S k (by omega) state hst)
    have hstate := linked_state_size bound hrun recovery hrec S k (by omega) state hst
    obtain ⟨iw, it, is, ih', il⟩ := ih (k + 1) hlinked (by omega)
    refine ⟨?_, ?_, ?_, ?_, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using il⟩
    · simp only [QuantitativeRealization.ExecutionTrace.cost, ExecutionCost.work_add, ExecutionCost.work_ofWork,
        ExecutionCost.work_observe, ExecutionCost.work_query]
      change Q.cost (headCode rep data cost primitive ports wports correction finalFn keys code R) state +
        Q.cost (updateCode rep data cost primitive ports wports correction finalFn keys code R) (state, ⟨position, direction⟩) +
        0 + 0 + tail.cost.work ≤ _
      nlinarith
    · simp only [QuantitativeRealization.ExecutionTrace.cost, ExecutionCost.traffic_add, ExecutionCost.traffic_ofWork,
        ExecutionCost.traffic_observe, ExecutionCost.traffic_query]
      change 0 + 0 + 0 + (Q.size bdI.pos position + Q.size bdI.idx ⟨position, direction⟩) + tail.cost.traffic ≤ _
      nlinarith
    · simp only [QuantitativeRealization.ExecutionTrace.cost, ExecutionCost.peakStateSize_add,
        ExecutionCost.peakStateSize_observe]
      change max (max (max (max 0 0) (Q.size (stateRep rep R) state)) 0) tail.cost.peakStateSize ≤ _
      omega
    · simp only [QuantitativeRealization.ExecutionTrace.cost, ExecutionCost.peakHeadSize_add,
        ExecutionCost.peakHeadSize_observe]
      change max (max (max (max 0 0) (Q.size (outerBoundary rep (bdI := bdI)).head ((wrapped correction finalFn keys R).head state))) 0)
        tail.cost.peakHeadSize ≤ _
      omega

/-- The wrapper runs within its derived budget whenever every run resolves within `cap` queries. -/
theorem runsWithin (hres : ∀ pk : G₂, (wrapped correction finalFn keys R).ResolvesIn cap ((wrapped correction finalFn keys R).init pk)) :
    (W).RunsWithin (fun _ => wrapExecution overhead width cap bound.peakStateSize routeWidth outputWidth finishedRoute
      adapterTime routineTime opTime comparisonTime bound.work) := by
  refine ⟨?_, ?_, ?_⟩
  · intro pk finish trace _
    have hinit0 : Linked R 0 ((W).machine.init pk) :=
      ⟨GeneralCaller.reachable_init R (keys pk), Nat.le_refl 0⟩
    have hlen := QuantitativeRealization.ExecutionTrace.length_le_of_resolvesIn trace (hres pk)
    obtain ⟨tw, tt, ts, th, hl⟩ := trace_bound bound hrun recovery hrec S 0 hinit0 trace (by omega)
    rw [Nat.zero_add] at hl
    obtain ⟨thead, hhead⟩ := headCode_cost S finish (wrapState_of_linked bound hrun recovery hrec S _ hlen finish hl)
    have hstate := linked_state_size bound hrun recovery hrec S _ hlen finish hl
    have tinit := initCode_cost S pk bound.work (innerInit_cost bound hrun (keys pk))
      (GeneralCaller.reachable_sizes R bound hrun _ (GeneralCaller.reachable_init R (keys pk))).1
    rw [executionCost_eq_init_add_trace_add_terminal]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [ExecutionCost.work_add, ExecutionCost.work_ofWork, terminalCost, ExecutionCost.work_observe, wrapExecution]
      change Q.cost (initCode rep data ports wports correction finalFn keys code R) pk + (trace.cost.work +
        (Q.cost (headCode rep data cost primitive ports wports correction finalFn keys code R) finish + 0)) ≤ _
      have hmul : trace.length * (HT + UT) ≤ cap * (HT + UT) := Nat.mul_le_mul_right _ hlen
      nlinarith
    · simp only [ExecutionCost.queries_add, ExecutionCost.queries_ofWork, terminalCost, ExecutionCost.queries_observe,
        QuantitativeRealization.ExecutionTrace.queries_cost, wrapExecution]
      omega
    · simp only [ExecutionCost.traffic_add, ExecutionCost.traffic_ofWork, terminalCost, ExecutionCost.traffic_observe, wrapExecution]
      have hmul : trace.length * (16 * width) ≤ cap * (16 * width) := Nat.mul_le_mul_right _ hlen
      omega
    · simp only [ExecutionCost.peakStateSize_add, terminalCost,
        ExecutionCost.peakStateSize_observe, wrapExecution]
      change max 0 (max trace.cost.peakStateSize (max 0 (Q.size (stateRep rep R) finish))) ≤ _
      omega
    · simp only [ExecutionCost.peakHeadSize_add, terminalCost,
        ExecutionCost.peakHeadSize_observe, wrapExecution]
      change max 0 (max trace.cost.peakHeadSize (max 0 (Q.size (outerBoundary rep (bdI := bdI)).head
        ((wrapped correction finalFn keys R).head finish)))) ≤ _
      omega
  · intro pk
    exact ((W).machine.resolvesInUnder_all_iff _ _).mpr (hres pk)
  · intro pk state _ _ position next _
    rcases position with (n | t) | m
    · exact ⟨⟨0, Nat.succ_pos _⟩, trivial⟩
    · exact ⟨0, trivial⟩
    · exact ⟨0, trivial⟩

end Signatures.Runtime.SyncWrapGeneral
