import Proofs.Runtime.GeneralSyncWrapSource
import Proofs.Runtime.BackendWeightedInterface
import Proofs.Runtime.BackendCaller
import Proofs.Runtime.Index
import Proofs.Runtime.Sampling
import Proofs.Runtime.Weakening

/-! # Executable code for the synchronized PS wrapper

The wrapper machine of `GeneralSyncWrapMachine.lean` is realized in the attacker's backend: its
state is the attacker's state paired with the recorded marks (and the pending period hash), its
readout and transition are assembled from the attacker's own three codes, the request and reply
adapters of the weighted interface, a few primitive operations, and compiled first-order code for
the finishing step. The semantic functions are spelled out first and shown to be the machine's
readout and flattened transition; the realizers then carry them by construction. -/

open OracleComp OracleSpec PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation
open Signatures.Runtime.WeightedAGM (GeneralRequest GeneralIndex BoundedRandomReply generalSpec
  generalPositions NativePorts tagRandom tagHash tagSign)
open Signatures.Runtime.BackendProgram

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
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {bdI : Boundary C (generalSpec (key.Value (cryptoBase F G₁ G₂ K M))
    (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor (G₂ × G₂)
    (OutTy.Value (cryptoBase F G₁ G₂ K M))}
  (ports : NativePorts (Q := Q) rep key Weights.syncMessage bdI)

attribute [local implicit_reducible] PFunctor.Idx

/-! ## Representations -/

/-- The general request positions, as the weighted interface represents them. -/
abbrev posRep := generalPositions rep key Weights.syncMessage randomBound

/-- Decoded tagged replies: a bounded random reply, a hashed period with its point, or a signed
message with its signature. -/
abbrev replyRep := StepClass.HasSum.sum ports.randomReply
  (StepClass.HasSum.sum (StepClass.HasProd.prod (rep.ty key) (rep.ty point₁))
    (StepClass.HasProd.prod (rep.ty Weights.syncMessage) (rep.ty point₁)))

variable (F G₁ G₂ K M randomBound) in
/-- The tagged reply's kind and payload. -/
def decodeIdx : GeneralIndex (key.Value (cryptoBase F G₁ G₂ K M)) (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M))
      G₁ randomBound →
    BoundedRandomReply randomBound ⊕ ((K × G₁) ⊕ ((K × F) × G₁))
  | ⟨.inl (.inl n), r⟩ => .inl ⟨n, r⟩
  | ⟨.inl (.inr t), h⟩ => .inr (.inl (t, h))
  | ⟨.inr m, σ⟩ => .inr (.inr (m, σ))

/-- Adapters between the attacker's boundary and the wrapper's native values. -/
structure WrapPorts where
  input : Q.Realizer (rep.ty (.pair point₂ point₂)) bdI.input id
  output : Q.Realizer bdI.out (rep.ty OutTy) id
  encode : Q.Realizer (rep.ty OutTy) bdI.out id
  position : Q.Realizer (posRep rep) bdI.pos id
  reply : Q.Realizer bdI.idx (replyRep rep ports) (decodeIdx F G₁ G₂ K M randomBound)

variable (correction finalFn : K × F → F) (keys : G₂ → G₂ × G₂)

/-- Executed correction, final scalar and key assembly of one weighted scheme. -/
structure SchemeCode where
  corr : Q.Realizer (rep.ty Weights.syncMessage) (rep.ty scalar) correction
  fin : Q.Realizer (rep.ty Weights.syncMessage) (rep.ty scalar) finalFn
  keys : Q.Realizer (rep.ty point₂) (rep.ty (.pair point₂ point₂)) keys

variable (R : GeneralCaller.Caller (Q := Q) (bd := bdI))

abbrev marksRep := rep.ty (.list markTy)
abbrev readyRep := StepClass.HasProd.prod R.state (marksRep rep)
abbrev gotRep := StepClass.HasProd.prod R.state (StepClass.HasProd.prod (rep.ty point₁) (marksRep rep))
abbrev doneRep := StepClass.HasProd.prod bdI.out (marksRep rep)
abbrev stateRep := StepClass.HasSum.sum (readyRep rep R) (StepClass.HasSum.sum (gotRep rep R) (doneRep rep (bdI := bdI)))

/-- The wrapped machine for this attacker. -/
abbrev wrapped : DynComputation (Spec F K G₁ randomBound).toPFunctor G₂ (OutTy.Value (cryptoBase F G₁ G₂ K M)) :=
  machine R.machine correction finalIndex (fin finalFn) keys

/-! ## Semantic readout and transition -/

/-- A pending request as the wrapper exposes it from a ready state. -/
def translatePos : GeneralRequest K (K × F) randomBound → GeneralRequest K (K × F) randomBound :=
  Sum.elim (fun l => .inl l) (fun m => .inl (.inr m.1))

/-- The readout from a ready state. -/
def headReadyFn (s : R.machine.State) : OutTy.Value (cryptoBase F G₁ G₂ K M) ⊕ GeneralRequest K (K × F) randomBound :=
  Sum.elim (fun result => .inr (.inl (.inr (finalIndex result)))) (fun pos => .inr (translatePos pos)) (R.machine.head s)

/-- The readout from a state waiting for a signature. -/
def headGotFn (s : R.machine.State) : OutTy.Value (cryptoBase F G₁ G₂ K M) ⊕ GeneralRequest K (K × F) randomBound :=
  Sum.elim (fun result => .inr (.inl (.inr (finalIndex result)))) (fun pos => .inr pos) (R.machine.head s)

def headFn : State R.machine (F := F) → OutTy.Value (cryptoBase F G₁ G₂ K M) ⊕ GeneralRequest K (K × F) randomBound
  | .inl (s, _) => headReadyFn R s
  | .inr (.inl (s, _, _)) => headGotFn R s
  | .inr (.inr (result, marks)) => .inl (fin finalFn result marks)

theorem headFn_eq : headFn finalFn R = (wrapped correction finalFn keys R).head := by
  funext st
  rw [head_eq_sumMap_view, view_ofStep]
  rcases st with ⟨s, marks⟩ | ⟨s, h, marks⟩ | ⟨result, marks⟩
  · rcases hv : R.machine.view s with result | ⟨(n | t) | m, next⟩ <;>
      simp [headFn, headReadyFn, translatePos, step, readyStep, hv, R.machine.head_eq_inl_of_view,
        R.machine.head_eq_inr_of_view]
  · rcases hv : R.machine.view s with result | ⟨(n | t) | m, next⟩ <;>
      simp [headFn, headGotFn, step, readyStep, hv, R.machine.head_eq_inl_of_view,
        R.machine.head_eq_inr_of_view]
  · rfl

/-- The transition from a ready state. -/
def updateReadyFn (s : R.machine.State) (marks : List (Mark F)) (idx : GeneralIndex K (K × F) G₁ randomBound) :
    Option (State R.machine (F := F)) :=
  match R.machine.head s with
  | .inl result =>
    match decodeIdx F G₁ G₂ K M randomBound idx with
    | .inr (.inl (t', _)) => if t' = finalIndex result then some (done R.machine result marks) else none
    | _ => none
  | .inr (.inl (.inl _)) => (R.machine.update? (s, idx)).map fun s' => ready R.machine s' marks
  | .inr (.inl (.inr _)) => (R.machine.update? (s, idx)).map fun s' => ready R.machine s' (markHash :: marks)
  | .inr (.inr m) =>
    match decodeIdx F G₁ G₂ K M randomBound idx with
    | .inr (.inl (t', h)) => if t' = m.1 then some (gotHash R.machine s h marks) else none
    | _ => none

/-- The transition from a state waiting for a signature. -/
def updateGotFn (s : R.machine.State) (h : G₁) (marks : List (Mark F)) (idx : GeneralIndex K (K × F) G₁ randomBound) :
    Option (State R.machine (F := F)) :=
  match R.machine.head s with
  | .inr (.inr _) =>
    match decodeIdx F G₁ G₂ K M randomBound idx with
    | .inr (.inr (m', σ)) =>
      (R.machine.update? (s, tagSign (m', σ + correction m' • h))).map fun s' =>
        ready R.machine s' (markSign correction m' :: marks)
    | _ => none
  | _ => updateReadyFn R s marks idx

def updateFn : State R.machine (F := F) × GeneralIndex K (K × F) G₁ randomBound → Option (State R.machine (F := F))
  | (.inl (s, marks), idx) => updateReadyFn R s marks idx
  | (.inr (.inl (s, h, marks)), idx) => updateGotFn correction R s h marks idx
  | (.inr (.inr _), _) => none

theorem updateReadyFn_eq (s : R.machine.State) (marks : List (Mark F)) (idx : GeneralIndex K (K × F) G₁ randomBound) :
    updateReadyFn R s marks idx = (wrapped correction finalFn keys R).update? (ready R.machine s marks, idx) := by
  obtain ⟨pos, reply⟩ := idx
  rcases hv : R.machine.view s with result | ⟨(n | t) | m, next⟩
  · have hview : (wrapped correction finalFn keys R).view (ready R.machine s marks) =
        .inr ⟨.inl (.inr (finalIndex result)), fun _ => done R.machine result marks⟩ := by
      rw [view_ofStep, step_ready, readyStep_inl R.machine finalIndex hv]
    simp only [updateReadyFn, R.machine.head_eq_inl_of_view hv]
    rcases pos with (n | t') | m'
    · rw [(wrapped correction finalFn keys R).update?_of_view_query_of_ne hview (by simp)]; rfl
    · by_cases ht : t' = finalIndex result
      · subst ht
        rw [(wrapped correction finalFn keys R).update?_of_view_query hview]
        simp [decodeIdx]
      · rw [(wrapped correction finalFn keys R).update?_of_view_query_of_ne hview (by simpa using ht)]
        simp [decodeIdx, ht]
    · rw [(wrapped correction finalFn keys R).update?_of_view_query_of_ne hview (by simp)]; rfl
  · have hview : (wrapped correction finalFn keys R).view (ready R.machine s marks) =
        .inr ⟨.inl (.inl n), fun r => ready R.machine (next r) marks⟩ := by
      rw [view_ofStep, step_ready, readyStep_random R.machine finalIndex hv]
    simp only [updateReadyFn, R.machine.head_eq_inr_of_view hv]
    unfold DynComputation.update?
    rw [hv, hview]
    simp only [Sum.elim_inr]
    split <;> rfl
  · have hview : (wrapped correction finalFn keys R).view (ready R.machine s marks) =
        .inr ⟨.inl (.inr t), fun h => ready R.machine (next h) (markHash :: marks)⟩ := by
      rw [view_ofStep, step_ready, readyStep_hash R.machine finalIndex hv]
    simp only [updateReadyFn, R.machine.head_eq_inr_of_view hv]
    unfold DynComputation.update?
    rw [hv, hview]
    simp only [Sum.elim_inr]
    split <;> rfl
  · have hview : (wrapped correction finalFn keys R).view (ready R.machine s marks) =
        .inr ⟨.inl (.inr m.1), fun (h : G₁) => gotHash R.machine s h marks⟩ := by
      rw [view_ofStep, step_ready, readyStep_sign R.machine finalIndex hv]
    simp only [updateReadyFn, R.machine.head_eq_inr_of_view hv]
    rcases pos with (n | t') | m'
    · rw [(wrapped correction finalFn keys R).update?_of_view_query_of_ne hview (by simp)]; rfl
    · by_cases ht : t' = m.1
      · subst ht
        rw [(wrapped correction finalFn keys R).update?_of_view_query hview]
        simp [decodeIdx]
      · rw [(wrapped correction finalFn keys R).update?_of_view_query_of_ne hview (by simpa using ht)]
        simp [decodeIdx, ht]
    · rw [(wrapped correction finalFn keys R).update?_of_view_query_of_ne hview (by simp)]; rfl

theorem updateGotFn_eq (s : R.machine.State) (h : G₁) (marks : List (Mark F))
    (idx : GeneralIndex K (K × F) G₁ randomBound) :
    updateGotFn correction R s h marks idx =
      (wrapped correction finalFn keys R).update? (gotHash R.machine s h marks, idx) := by
  obtain ⟨pos, reply⟩ := idx
  rcases hv : R.machine.view s with result | ⟨(n | t) | m, next⟩
  · have hstep : step R.machine correction finalIndex (fin finalFn) (gotHash R.machine s h marks) =
        step R.machine correction finalIndex (fin finalFn) (ready R.machine s marks) := by
      simp only [step, hv]
    simp only [updateGotFn, R.machine.head_eq_inl_of_view hv]
    rw [updateReadyFn_eq correction finalFn keys]
    unfold DynComputation.update?
    rw [view_ofStep, view_ofStep, hstep]
  · have hstep : step R.machine correction finalIndex (fin finalFn) (gotHash R.machine s h marks) =
        step R.machine correction finalIndex (fin finalFn) (ready R.machine s marks) := by
      simp only [step, hv]
    simp only [updateGotFn, R.machine.head_eq_inr_of_view hv]
    rw [updateReadyFn_eq correction finalFn keys]
    unfold DynComputation.update?
    rw [view_ofStep, view_ofStep, hstep]
  · have hstep : step R.machine correction finalIndex (fin finalFn) (gotHash R.machine s h marks) =
        step R.machine correction finalIndex (fin finalFn) (ready R.machine s marks) := by
      simp only [step, hv]
    simp only [updateGotFn, R.machine.head_eq_inr_of_view hv]
    rw [updateReadyFn_eq correction finalFn keys]
    unfold DynComputation.update?
    rw [view_ofStep, view_ofStep, hstep]
  · have hview : (wrapped correction finalFn keys R).view (gotHash R.machine s h marks) =
        .inr ⟨.inr m, fun (σ : G₁) => ready R.machine (next (σ + correction m • h)) (markSign correction m :: marks)⟩ := by
      rw [view_ofStep, step_gotHash R.machine correction finalIndex (fin finalFn) hv]
    simp only [updateGotFn, R.machine.head_eq_inr_of_view hv]
    rcases pos with (n | t') | m'
    · rw [(wrapped correction finalFn keys R).update?_of_view_query_of_ne hview (by simp)]; rfl
    · rw [(wrapped correction finalFn keys R).update?_of_view_query_of_ne hview (by simp)]; rfl
    · by_cases hm : m' = m
      · subst hm
        rw [(wrapped correction finalFn keys R).update?_of_view_query hview]
        simp only [decodeIdx, tagSign]
        rw [R.machine.update?_of_view_query hv]
        rfl
      · rw [(wrapped correction finalFn keys R).update?_of_view_query_of_ne hview (by simpa using hm)]
        simp only [decodeIdx, tagSign]
        rw [R.machine.update?_of_view_query_of_ne hv (by simpa using hm)]
        rfl

theorem updateFn_eq : updateFn correction R = (wrapped correction finalFn keys R).update? := by
  funext step
  obtain ⟨st, idx⟩ := step
  rcases st with ⟨s, marks⟩ | ⟨s, h, marks⟩ | ⟨result, marks⟩
  · exact updateReadyFn_eq correction finalFn keys R s marks idx
  · exact updateGotFn_eq correction finalFn keys R s h marks idx
  · rw [(wrapped correction finalFn keys R).update?_of_view_return (value := fin finalFn result marks) rfl]
    rfl

end Signatures.Runtime.SyncWrapGeneral
