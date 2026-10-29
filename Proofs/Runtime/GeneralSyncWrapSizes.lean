import Proofs.Runtime.GeneralSyncWrapCaps
import Proofs.Runtime.GeneralSyncWrapFinishCost
import Proofs.Runtime.BackendFrameCost
import Proofs.Runtime.BackendWeightedHandlerBudget

/-! # Sizes of the wrapper's values at one frame

Every value the wrapper's codes touch is bounded by one frame width built from the attacker's
own state and readout widths, the decoded output width, the finished output's encoding and the
marks. The facts here are the size side conditions of the structural cost laws, stated once. -/

open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation
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
  {bdI : Boundary C (generalSpec (key.Value (cryptoBase F G₁ G₂ K M))
    (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor (G₂ × G₂)
    (OutTy.Value (cryptoBase F G₁ G₂ K M))}
  (ports : NativePorts (Q := Q) rep key Weights.syncMessage bdI)
  (wports : WrapPorts rep ports)
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (R : GeneralCaller.Caller (Q := Q) (bd := bdI))

attribute [local implicit_reducible] PFunctor.Idx

local notation "prod" => StepClass.HasProd.prod
local notation "sum" => StepClass.HasSum.sum
local notation "opt" => StepClass.HasOption.option

/-- The frame: eight times every component width plus room for the small values. -/
def wrapFrame (width cap stateWidth routeWidth outputWidth finishedRoute : Nat) : Nat :=
  8 * (stateWidth + routeWidth + outputWidth + finishedRoute) + 8 * marksWidth width (cap + 1) + 64 * width

/-- The encoded width of the finished output: three output components, the remapped
coefficients and headers. -/
def finishedWidth (width cap outputWidth : Nat) : Nat := 3 * outputWidth + (2 * cap + 6) * width

theorem marksWidth_le_succ (width cap : Nat) : marksWidth width cap ≤ marksWidth width (cap + 1) := by
  unfold marksWidth
  exact Nat.mul_le_mul_right width (by omega)

/-! ## The attacker's values -/

variable (width cap stateWidth headWidth routeWidth outputWidth finishedRoute : Nat)

local notation "WF" => wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute

theorem width_le_frame : width ≤ WF := by unfold wrapFrame; omega
theorem eight_width_le_frame : 8 * width ≤ WF := by unfold wrapFrame; omega
theorem room_le_frame : 64 * width ≤ WF := by unfold wrapFrame; omega
theorem inner_le_frame : stateWidth ≤ WF := by unfold wrapFrame; omega
theorem route_le_frame : routeWidth ≤ WF := by unfold wrapFrame; omega
theorem output_le_frame : outputWidth ≤ WF := by unfold wrapFrame; omega
theorem finished_le_frame : finishedRoute ≤ WF := by unfold wrapFrame; omega
theorem marks_le_frame : marksWidth width (cap + 1) ≤ WF := by unfold wrapFrame; omega

include sizes

theorem pair_size {A B : Type} (a : C.Str A) (b : C.Str B) (x : A) (y : B) {wa wb : Nat}
    (ha : Q.size a x ≤ wa) (hb : Q.size b y ≤ wb) : Q.size (prod a b) (x, y) ≤ wa + wb + header := by
  have h := sizes.prod_le a b (x, y)
  dsimp only at h
  omega

theorem inl_size {A B : Type} (a : C.Str A) (b : C.Str B) (x : A) {wa : Nat} (ha : Q.size a x ≤ wa) :
    Q.size (sum a b) (.inl x) ≤ wa + header := by
  have h := sizes.sum_le a b (.inl x)
  simp only [Sum.elim_inl] at h
  omega

theorem inr_size {A B : Type} (a : C.Str A) (b : C.Str B) (y : B) {wb : Nat} (hb : Q.size b y ≤ wb) :
    Q.size (sum a b) (.inr y) ≤ wb + header := by
  have h := sizes.sum_le a b (.inr y)
  simp only [Sum.elim_inr] at h
  omega

theorem some_size {A : Type} (a : C.Str A) (x : A) {wa : Nat} (ha : Q.size a x ≤ wa) :
    Q.size (opt a) (some x) ≤ wa + header :=
  (sizes.some_le a x).trans (by omega)

theorem none_size {A : Type} (a : C.Str A) : Q.size (opt a) none ≤ header := sizes.none_le a

theorem inl_payload {A B : Type} (a : C.Str A) (b : C.Str B) (x : A) {w : Nat}
    (h : Q.size (sum a b) (.inl x) ≤ w) : Q.size a x ≤ w :=
  (by simpa using sizes.sum_payload_le a b (.inl x) : Q.size a x ≤ Q.size (sum a b) (.inl x)).trans h

theorem inr_payload {A B : Type} (a : C.Str A) (b : C.Str B) (y : B) {w : Nat}
    (h : Q.size (sum a b) (.inr y) ≤ w) : Q.size b y ≤ w :=
  (by simpa using sizes.sum_payload_le a b (.inr y) : Q.size b y ≤ Q.size (sum a b) (.inr y)).trans h

/-- A ready state with bounded components sits in the frame, with room for pairing it with a
tagged reply. -/
theorem ready_le_frame (hh : header ≤ width) (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth)
    (marks : List (Mark F)) (hm : Q.size (marksRep rep) marks ≤ marksWidth width (cap + 1)) :
    Q.size (readyRep rep R) (s, marks) + 16 * width ≤ WF := by
  have h := pair_size sizes R.state (marksRep rep) s marks hs hm
  change Q.size (readyRep rep R) (s, marks) ≤ _ at h
  unfold wrapFrame; omega

theorem got_le_frame (hh : header ≤ width) (hp : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (h : G₁)
    (marks : List (Mark F)) (hm : Q.size (marksRep rep) marks ≤ marksWidth width (cap + 1)) :
    Q.size (gotRep rep R) (s, h, marks) + 16 * width ≤ WF := by
  have h1 := pair_size sizes (rep.ty point₁) (marksRep rep) h marks (hp h) hm
  have h2 := pair_size sizes R.state (prod (rep.ty point₁) (marksRep rep)) s (h, marks) hs h1
  change Q.size (gotRep rep R) (s, h, marks) ≤ _ at h2
  unfold wrapFrame; omega

theorem done_le_frame (hh : header ≤ width) (hHR : headWidth ≤ routeWidth) (result : OutTy.Value (cryptoBase F G₁ G₂ K M))
    (hr : Q.size bdI.out result ≤ headWidth)
    (marks : List (Mark F)) (hm : Q.size (marksRep rep) marks ≤ marksWidth width (cap + 1)) :
    Q.size (doneRep rep (bdI := bdI)) (result, marks) + 16 * width ≤ WF := by
  have h := pair_size sizes bdI.out (marksRep rep) result marks hr hm
  change Q.size (doneRep rep (bdI := bdI)) (result, marks) ≤ _ at h
  unfold wrapFrame; omega

end Signatures.Runtime.SyncWrapGeneral
