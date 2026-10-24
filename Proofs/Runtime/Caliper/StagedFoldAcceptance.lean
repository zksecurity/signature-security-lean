import Proofs.Runtime.Caliper.StagedFoldBounds
import Proofs.Runtime.Caliper.BufferBounds

/-! Successful staged-fold emission from bounded local bodies. The scratch
namespace is reused between stages and does not grow with traversal capacity. -/

namespace Signatures.Runtime.CaliperBackend
open Caliper BoundedSource

variable {w : Nat}

theorem FoldStep.buffers (body following stop : Stmt w) (entry state next env capacity : Nat) :
    (FoldStep.code body following stop (max 2 body.memBound) entry state next env capacity).memBound ≤
      max (max 2 body.memBound + 1) (max following.memBound stop.memBound) := by
  have prepared := ListFold.prepare_buffers (w := w) entry state env capacity
  have retained := (Retain.code_names body (max 2 body.memBound)
    (entry + (state + env)) next (1 + capacity * entry + env)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)).2
  have reordered := Reorder.buffers (w := w) next (1 + capacity * entry) env
  have finished := selectSlice_buffers (w := w) (1 + (capacity + 1) * entry) state
  simp only [FoldStep.code, Stmt.memBound]
  omega

namespace BoundedSource.StagedFold
variable {A B E : Type} {cost : CostModel}

theorem accept (allocation : 1 ≤ cost.allocPerWord) (entry : Layout w A) (result : Layout w B)
    (env : Layout w E) (hw : 16 < 2 ^ w) (f : A × (B × E) → B)
    (capacity : Nat) (states : Fin (capacity + 1) → Layout w B)
    (countFits : capacity < 2 ^ w)
    (argFits : ∀ i : Fin capacity,
      entry.representation.encoding.words + (states i.castSucc).representation.encoding.words + env.representation.encoding.words < 2 ^ w)
    (frameFits : ∀ i : Fin (capacity + 1),
      1 + (capacity - i.val) * entry.representation.encoding.words + (states i).representation.encoding.words +
        2 * env.representation.encoding.words < 2 ^ w)
    (bodies : ∀ i : Fin capacity, Implementation cost
      (FoldImplementation.bodyInput entry (states i.castSucc) env (argFits i)) (states i.succ) f)
    (stops : ∀ i : Fin (capacity + 1), Implementation cost (states i) result id)
    (bodyBuffers stopBuffers : Nat)
    (bodyBound : ∀ i, (bodies i).program.code.memBound ≤ bodyBuffers)
    (stopBound : ∀ i, (stops i).program.code.memBound ≤ stopBuffers)
    (namesFit : bodyBuffers < 2 ^ w) :
    ∃ implementation, compile allocation entry result env hw f capacity states countFits argFits frameFits
      (fun i => some (bodies i)) stops = some implementation ∧
      implementation.program.code.memBound ≤ max (max 2 bodyBuffers + 1) stopBuffers := by
  induction capacity with
  | zero =>
    refine ⟨finish allocation entry (states 0) result env hw (frameFits 0) (stops 0) f, rfl, ?_⟩
    have selected := selectSlice_buffers (w := w) (1 + 0 * entry.representation.encoding.words) (states 0).representation.encoding.words
    have stopped := stopBound 0
    change max (selectSlice (w := w) (1 + 0 * entry.representation.encoding.words) (states 0).representation.encoding.words).memBound
      (stops 0).program.code.memBound ≤ max (max 2 bodyBuffers + 1) stopBuffers
    exact max_le (selected.trans (by omega)) (stopped.trans (by omega))
  | succ capacity ih =>
    obtain ⟨following, gotFollowing, followingBound⟩ := ih (fun i => states i.succ) (by omega)
      (fun i => argFits i.succ)
      (fun i => by simpa only [Fin.val_succ, Nat.add_sub_add_right] using frameFits i.succ)
      (fun i => bodies i.succ) (fun i => stops i.succ)
      (fun i => bodyBound i.succ) (fun i => stopBound i.succ)
    have nameFits : (bodies 0).program.savedBuffer < 2 ^ w := by
      have bounded := bodyBound 0
      dsimp only [Realizer.savedBuffer]
      omega
    refine ⟨step entry (states 0) (states 1) result env capacity hw countFits (argFits 0) (frameFits 0)
      (by simpa only [Fin.val_one, Nat.add_sub_cancel_right] using frameFits 1)
      (bodies 0) following (stops 0) allocation nameFits, ?_, ?_⟩
    · simp only [compile, Option.bind_eq_bind, Option.bind_eq_some_iff]
      exact ⟨bodies 0, rfl, following, gotFollowing, dite_eq_left nameFits⟩
    · have bounded := FoldStep.buffers (bodies 0).program.code following.program.code (stops 0).program.code
        entry.representation.encoding.words (states 0).representation.encoding.words
        (states 1).representation.encoding.words env.representation.encoding.words capacity
      have current := bodyBound 0
      have stopped := stopBound 0
      exact bounded.trans (by omega)

end BoundedSource.StagedFold
end Signatures.Runtime.CaliperBackend
