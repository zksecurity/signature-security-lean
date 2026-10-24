import Proofs.Runtime.BackendLocalBound
import Proofs.Runtime.BackendCaller

/-! Derive caller-routing costs from its actual local work and backend data
operations. Arbitrary computation in the caller's head/update code remains
charged at its measured backend cost. The added work is explicitly represented
by structural operations on encoded caller, request, reply, and wrapper values.
-/

open PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]

structure DispatchCostLaws (overhead : Nat → Nat) : Prop where
  inl : ∀ {A B : Type} (a : C.Str A) (b : C.Str B) (input : A),
    Q.cost (QS.inl a b) input ≤ overhead (Q.size a input + Q.size (StepClass.HasSum.sum a b) (.inl input))
  inr : ∀ {A B : Type} (a : C.Str A) (b : C.Str B) (input : B),
    Q.cost (QS.inr a b) input ≤ overhead (Q.size b input + Q.size (StepClass.HasSum.sum a b) (.inr input))
  none : ∀ {A B : Type} (a : C.Str A) (b : C.Str B) (input : A),
    Q.cost (QO.none a b) input ≤ overhead (Q.size a input + Q.size (StepClass.HasOption.option b) none)
  some : ∀ {A : Type} (a : C.Str A) (input : A),
    Q.cost (OC.someCode a) input ≤ overhead (Q.size a input + Q.size (StepClass.HasOption.option a) (some input))
  getD : ∀ {A : Type} (a : C.Str A) (input : Option A × A),
    Q.cost (OC.getDCode a) input ≤ overhead
      (Q.size (StepClass.HasProd.prod (StepClass.HasOption.option a) a) input + Q.size a (input.1.getD input.2))
  distribute : ∀ {A B E : Type} (a : C.Str A) (b : C.Str B) (e : C.Str E) (input : (A ⊕ B) × E),
    Q.cost (QD.distribute a b e) input ≤ overhead
      (Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum a b) e) input +
        Q.size (StepClass.HasSum.sum (StepClass.HasProd.prod a e) (StepClass.HasProd.prod b e))
          (Sum.elim (fun left => Sum.inl (left, input.2)) (fun right => Sum.inr (right, input.2)) input.1))

namespace DispatchCostLaws

variable {overhead : Nat → Nat} (laws : DispatchCostLaws (Q := Q) overhead)

def inlBound {A B : Type} (a : C.Str A) (b : C.Str B) : LocalBound (QS.inl a b) where
  time input := overhead (Q.size a input + Q.size (StepClass.HasSum.sum a b) (.inl input))
  cost_le := laws.inl a b

def inrBound {A B : Type} (a : C.Str A) (b : C.Str B) : LocalBound (QS.inr a b) where
  time input := overhead (Q.size b input + Q.size (StepClass.HasSum.sum a b) (.inr input))
  cost_le := laws.inr a b

def noneBound {A B : Type} (a : C.Str A) (b : C.Str B) : LocalBound (QO.none a b) where
  time input := overhead (Q.size a input + Q.size (StepClass.HasOption.option b) Option.none)
  cost_le := laws.none a b

def someBound {A : Type} (a : C.Str A) : LocalBound (OC.someCode a) where
  time input := overhead (Q.size a input + Q.size (StepClass.HasOption.option a) (Option.some input))
  cost_le := laws.some a

def getDBound {A : Type} (a : C.Str A) : LocalBound (OC.getDCode a) where
  time input := overhead
    (Q.size (StepClass.HasProd.prod (StepClass.HasOption.option a) a) input + Q.size a (input.1.getD input.2))
  cost_le := laws.getD a

def distributeBound {A B E : Type} (a : C.Str A) (b : C.Str B) (e : C.Str E) :
    LocalBound (QD.distribute a b e) where
  time input := overhead
    (Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum a b) e) input +
      Q.size (StepClass.HasSum.sum (StepClass.HasProd.prod a e) (StepClass.HasProd.prod b e))
        (Sum.elim (fun left => Sum.inl (left, input.2)) (fun right => Sum.inr (right, input.2)) input.1))
  cost_le := laws.distribute a b e

end DispatchCostLaws

namespace Caller

variable {I A B S : Type} {source : OracleSpec I} [DecidableEq I]
  {bd : Boundary C source.toPFunctor A B}
  (R : GeneralCaller.Caller (Q := Q) (bd := bd)) (store : C.Str S)
  {overhead : Nat → Nat} (localLaws : LocalCostLaws Q overhead)
  (dispatchLaws : DispatchCostLaws (Q := Q) overhead)

def inspectBound : LocalBound (inspectCode R store) :=
  LocalBound.compose localLaws
    (LocalBound.pair localLaws
      (LocalBound.compose localLaws (LocalBound.fst localLaws _ _) (LocalBound.measured R.headCode))
      (LocalBound.identity localLaws _)) (dispatchLaws.distributeBound _ _ _)

def doneBound : LocalBound (doneCode R store) :=
  LocalBound.pair localLaws
    (LocalBound.compose localLaws (LocalBound.fst localLaws _ _) (dispatchLaws.someBound _))
    (LocalBound.compose localLaws (LocalBound.snd localLaws _ _) (LocalBound.snd localLaws _ _))

def queryArgsBound : LocalBound (queryArgsCode R store) :=
  LocalBound.pair localLaws
    (LocalBound.pair localLaws (LocalBound.fst localLaws _ _)
      (LocalBound.compose localLaws (LocalBound.snd localLaws _ _) (LocalBound.snd localLaws _ _)))
    (LocalBound.compose localLaws (LocalBound.snd localLaws _ _) (LocalBound.fst localLaws _ _))

def resumeArgsBound : LocalBound (resumeArgsCode R store) :=
  LocalBound.pair localLaws
    (LocalBound.pair localLaws (LocalBound.snd localLaws _ _)
      (LocalBound.compose localLaws (LocalBound.fst localLaws _ _) (LocalBound.fst localLaws _ _)))
    (LocalBound.compose localLaws (LocalBound.fst localLaws _ _) (LocalBound.snd localLaws _ _))

def updateBound : LocalBound (updateCode R) :=
  LocalBound.compose localLaws
    (LocalBound.pair localLaws (LocalBound.measured R.updateCode) (LocalBound.fst localLaws _ _))
    (dispatchLaws.getDBound _)

def cutoffBound : LocalBound (cutoffCode R store) :=
  LocalBound.pair localLaws (dispatchLaws.noneBound _ _)
    (LocalBound.compose localLaws (LocalBound.snd localLaws _ _) (LocalBound.snd localLaws _ _))

/-- Sizes charged when inspecting a caller head and retaining its state. -/
def inspectSizes (input : R.machine.State × S) : List Nat :=
  let inputSize := Q.size (frame R store) input
  let stateSize := Q.size R.state input.1
  let head := R.machine.head input.1
  let headSize := Q.size bd.head head
  let pairSize := Q.size (StepClass.HasProd.prod bd.head (frame R store)) (head, input)
  let resultSize := Q.size
    (StepClass.HasSum.sum (StepClass.HasProd.prod bd.out (frame R store))
      (StepClass.HasProd.prod bd.pos (frame R store)))
    (Sum.elim (fun value => Sum.inl (value, input)) (fun position => Sum.inr (position, input)) head)
  [inputSize + stateSize, inputSize + stateSize + headSize, inputSize,
    inputSize + pairSize, pairSize + resultSize, inputSize + pairSize + resultSize]

theorem inspectBound_time (input : R.machine.State × S) :
    (inspectBound R store localLaws dispatchLaws).time input =
      Q.cost R.headCode input.1 + ((inspectSizes R store input).map overhead).sum := by
  dsimp [inspectBound, LocalBound.compose, LocalBound.pair, LocalBound.fst,
    LocalBound.identity, LocalBound.measured, DispatchCostLaws.distributeBound, inspectSizes,
    frame, Boundary.head]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- Sizes charged when installing the next state after a matching reply. -/
def updateSizes (input : R.machine.State × source.toPFunctor.Idx) : List Nat :=
  let inputSize := Q.size (bd.stateIdx R.state) input
  let stateSize := Q.size R.state input.1
  let next := R.machine.update? input
  let pairSize := Q.size (StepClass.HasProd.prod (StepClass.HasOption.option R.state) R.state) (next, input.1)
  let outputSize := Q.size R.state (next.getD input.1)
  [inputSize + stateSize, inputSize + pairSize, pairSize + outputSize, inputSize + pairSize + outputSize]

theorem updateBound_time (input : R.machine.State × source.toPFunctor.Idx) :
    (updateBound R localLaws dispatchLaws).time input =
      Q.cost R.updateCode input + ((updateSizes R input).map overhead).sum := by
  dsimp [updateBound, LocalBound.compose, LocalBound.pair, LocalBound.fst,
    LocalBound.measured, DispatchCostLaws.getDBound, updateSizes, Boundary.stateIdx]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

private theorem sum_fees_le (sizes : List Nat) (overhead : Nat → Nat) (tick : Nat)
    (h : ∀ n ∈ sizes, overhead n ≤ tick) : (sizes.map overhead).sum ≤ sizes.length * tick := by
  induction sizes with
  | nil => simp
  | cons n sizes ih =>
      have hn := h n (by simp)
      have ht := ih (fun k hk => h k (by simp [hk]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

include localLaws dispatchLaws

/-- Inspection adds six size-bounded structural charges to the caller's actual
head computation. It does not bound that arbitrary computation by a constant. -/
theorem inspect_cost_le (input : R.machine.State × S) (width tick : Nat)
    (hs : ∀ n ∈ inspectSizes R store input, n ≤ width)
    (hf : ∀ n ≤ width, overhead n ≤ tick) :
    Q.cost (inspectCode R store) input ≤ Q.cost R.headCode input.1 + 6 * tick := by
  have h := (inspectBound R store localLaws dispatchLaws).cost_le input
  rw [inspectBound_time] at h
  have ht := sum_fees_le (inspectSizes R store input) overhead tick (fun n hn => hf n (hs n hn))
  have hl : (inspectSizes R store input).length = 6 := rfl
  rw [hl] at ht
  omega

/-- Updating adds four size-bounded structural charges to the caller's actual
enabled-update computation. Reply construction and handler work are separate. -/
theorem update_cost_le (input : R.machine.State × source.toPFunctor.Idx) (width tick : Nat)
    (hs : ∀ n ∈ updateSizes R input, n ≤ width)
    (hf : ∀ n ≤ width, overhead n ≤ tick) :
    Q.cost (updateCode R) input ≤ Q.cost R.updateCode input + 4 * tick := by
  have h := (updateBound R localLaws dispatchLaws).cost_le input
  rw [updateBound_time] at h
  have ht := sum_fees_le (updateSizes R input) overhead tick (fun n hn => hf n (hs n hn))
  have hl : (updateSizes R input).length = 4 := rfl
  rw [hl] at ht
  omega

end Caller

end Signatures.Runtime.BackendProgram
