import Proofs.Runtime.Caliper.SourceFoldBudgets

/-! Uniform polynomial budgets for complete, accepted staged folds. The only
input budgets concern the individual body and final-conversion implementations.
The generated fold's stored branches and copies are included in the conclusion. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.StagedFold

open Caliper

variable {w : Nat} {A B E : Type}

def frameBound (layoutWords capacity : Nat) : Nat := 1 + (capacity + 5) * layoutWords

def timeBudget (layoutWords bodyTime stopTime capacity : Nat) : Nat :=
  8 * layoutWords + stopTime + capacity * (bodyTime + stopTime + 44 * frameBound layoutWords capacity + 7)

def codeBudget (layoutWords bodyWords stopWords capacity : Nat) : Nat :=
  26 * layoutWords + 15 + stopWords + capacity * (bodyWords + stopWords + 169 * frameBound layoutWords capacity + 116)

theorem compile_boundedBy (entry : Layout w A) (result : Layout w B) (env : Layout w E)
    (hw : 16 < 2 ^ w) (f : A × (B × E) → B)
    (capacity : Nat) (states : Fin (capacity + 1) → Layout w B)
    (countFits : capacity < 2 ^ w)
    (argFits : ∀ i : Fin capacity,
      entry.representation.encoding.words + (states i.castSucc).representation.encoding.words + env.representation.encoding.words < 2 ^ w)
    (frameFits : ∀ i : Fin (capacity + 1),
      1 + (capacity - i.val) * entry.representation.encoding.words + (states i).representation.encoding.words +
        2 * env.representation.encoding.words < 2 ^ w)
    (bodies : ∀ i : Fin capacity, Option (Implementation .unit
      (FoldImplementation.bodyInput entry (states i.castSucc) env (argFits i)) (states i.succ) f))
    (stops : ∀ i : Fin (capacity + 1), Implementation .unit (states i) result id)
    (layoutWords bodyTime bodyWords stopTime stopWords : Nat)
    (entryBound : entry.representation.encoding.words ≤ layoutWords)
    (envBound : env.representation.encoding.words ≤ layoutWords)
    (stateBound : ∀ i, (states i).representation.encoding.words ≤ layoutWords)
    (bodyBound : ∀ i body, bodies i = some body → body.BoundedBy bodyTime bodyWords)
    (stopBound : ∀ i, (stops i).BoundedBy stopTime stopWords)
    (implementation : Implementation .unit
      (FoldImplementation.input entry (states 0) env capacity countFits (frameFits 0)) result (FoldImplementation.sourceFold f))
    (compiled : compile (by decide) entry result env hw f capacity states countFits argFits frameFits bodies stops = some implementation) :
    implementation.BoundedBy (timeBudget layoutWords bodyTime stopTime capacity)
      (codeBudget layoutWords bodyWords stopWords capacity) := by
  induction capacity with
  | zero =>
    simp only [compile] at compiled
    cases Option.some.inj compiled
    exact (finish_boundedBy entry (states 0) result env hw (frameFits 0) (stops 0) f stopTime stopWords (stopBound 0)).mono
      (by dsimp [timeBudget]; have bound := stateBound 0; omega)
      (by dsimp [codeBudget]; have bound := stateBound 0; omega)
  | succ capacity ih =>
    simp only [compile, Option.bind_eq_bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨body, gotBody, following, gotFollowing, compiled⟩ := compiled
    split at compiled
    next nameFits =>
      cases Option.some.inj compiled
      have followingBound := ih (fun i => states i.succ) (by omega)
        (fun i => argFits i.succ)
        (fun i => by simpa only [Fin.val_succ, Nat.add_sub_add_right] using frameFits i.succ)
        (fun i => bodies i.succ) (fun i => stops i.succ)
        (fun i => stateBound i.succ) (fun i body got => bodyBound i.succ body got)
        (fun i => stopBound i.succ) following gotFollowing
      have stage := step_boundedBy entry (states 0) (states 1) result env capacity hw countFits (argFits 0) (frameFits 0)
        (by simpa only [Fin.val_one, Nat.add_sub_cancel_right] using frameFits 1)
        body following (stops 0) nameFits bodyTime bodyWords
        (timeBudget layoutWords bodyTime stopTime capacity) (codeBudget layoutWords bodyWords stopWords capacity)
        stopTime stopWords (bodyBound 0 body gotBody) followingBound (stopBound 0)
      have widthBound : FoldStep.width entry.representation.encoding.words (states 0).representation.encoding.words
          (states 1).representation.encoding.words env.representation.encoding.words capacity ≤ frameBound layoutWords (capacity + 1) := by
        have current := stateBound 0
        have next := stateBound 1
        have entries := Nat.mul_le_mul_left (capacity + 1) entryBound
        dsimp [FoldStep.width, frameBound]
        nlinarith
      have widthMono : frameBound layoutWords capacity ≤ frameBound layoutWords (capacity + 1) := by
        dsimp [frameBound]
        nlinarith
      apply stage.mono
      · have monotone := Nat.mul_le_mul_left capacity (show bodyTime + stopTime + 44 * frameBound layoutWords capacity + 7 ≤
            bodyTime + stopTime + 44 * frameBound layoutWords (capacity + 1) + 7 by omega)
        dsimp only [timeBudget]
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · have monotone := Nat.mul_le_mul_left capacity (show bodyWords + stopWords + 169 * frameBound layoutWords capacity + 116 ≤
            bodyWords + stopWords + 169 * frameBound layoutWords (capacity + 1) + 116 by omega)
        dsimp only [codeBudget]
        rw [Nat.add_mul, Nat.one_mul]
        omega
    next rejected => contradiction

end Signatures.Runtime.CaliperBackend.BoundedSource.StagedFold
