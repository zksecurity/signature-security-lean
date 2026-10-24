import Proofs.Runtime.Caliper.StructuralNames

/-! Dense name bounds for the complete staged fold. Each stage reuses its
callee-relative saved-buffer reservation; stages do not allocate a name range
indexed by the message domain. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.StagedFold

open Caliper

variable {w : Nat} {A B E : Type}

theorem compile_names (entry : Layout w A) (result : Layout w B) (env : Layout w E)
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
    (slots : Nat)
    (bodyBound : ∀ i body, bodies i = some body → NamesAccounted body.program.code slots)
    (stopBound : ∀ i, NamesAccounted (stops i).program.code slots)
    (implementation : Implementation .unit
      (FoldImplementation.input entry (states 0) env capacity countFits (frameFits 0)) result (FoldImplementation.sourceFold f))
    (compiled : compile (by decide) entry result env hw f capacity states countFits argFits frameFits bodies stops = some implementation) :
    NamesAccounted implementation.program.code slots := by
  induction capacity with
  | zero =>
    simp only [compile] at compiled
    cases Option.some.inj compiled
    exact (selectSlice_names _ _ _).seq (stopBound 0)
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
        (fun i body got => bodyBound i.succ body got) (fun i => stopBound i.succ) following gotFollowing
      exact FoldStep.names (bodyBound 0 body gotBody) followingBound (stopBound 0) _ _ _ _ _
    next rejected => contradiction

end Signatures.Runtime.CaliperBackend.BoundedSource.StagedFold
