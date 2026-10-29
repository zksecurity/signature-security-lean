import Proofs.Runtime.GeneralWeighted
import Proofs.Model.MachineView
import Proofs.SynchronizedPS.WrapMachine

/-! # The synchronized PS wrapper as a general-interface oracle machine

`SynchronizedPS/WrapMachine.lean` wraps an inner attacker machine over the lazy AGM interface.
General callers of the weighted pipeline speak the bounded-randomness interface `generalSpec`
instead, so this file repeats the construction there: the wrapper forwards randomness and hash
requests, answers a signing request by first exposing the hash of its period and then the signing
request itself, feeding the corrected reply to the inner machine, and after the inner machine
returns it exposes one last hash and finishes. The known key is fixed in the correction and
finishing functions, so the machine's input is the weighted public key alone. Marks are the
wrapper's record of answered hash and signing requests, newest first so that recording is one
cons; they are pairs so that finishing code can be compiled from the first-order expression
language. The state is a sum of products for
the same reason. Implementation is a view-level simulation, and the query budget grows by one
per signing request plus the final hash. -/

open OracleComp OracleSpec PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation
open Signatures.Runtime.WeightedAGM (GeneralRequest generalSpec)

namespace Signatures.Runtime.SyncWrapGeneral

set_option linter.unusedSectionVars false

variable {F K G₁ : Type} [Field F] [AddCommGroup G₁] [Module F G₁] {randomBound : Nat}

/-- One mark per answered request: `(false, 0)` after a hash, `(true, correction m)` after a
signature on `m`. -/
abbrev Mark (F : Type) := Bool × F

variable (F K G₁ randomBound) in
abbrev Spec := generalSpec K (K × F) G₁ randomBound

variable {In Out α : Type}
  (M : DynComputation (Spec F K G₁ randomBound).toPFunctor α In)
  (correction : K × F → F) (finalIndex : In → K) (fin : In → List (Mark F) → Out)

/-- Ready with the inner state, waiting for a signing reply with the period's hash in hand, or
done with the inner result. -/
abbrev State := (M.State × List (Mark F)) ⊕ ((M.State × (G₁ × List (Mark F))) ⊕ (In × List (Mark F)))

@[reducible] def ready (s : M.State) (marks : List (Mark F)) : State M := .inl (s, marks)
@[reducible] def gotHash (s : M.State) (point : G₁) (marks : List (Mark F)) : State M :=
  .inr (.inl (s, (point, marks)))
@[reducible] def done (result : In) (marks : List (Mark F)) : State M := .inr (.inr (result, marks))

def markHash : Mark F := (false, 0)
def markSign (m : K × F) : Mark F := (true, correction m)

/-- The step out of a ready state, in terms of the inner machine's view. -/
def readyStep (s : M.State) (marks : List (Mark F)) :
    Out ⊕ (Spec F K G₁ randomBound).toPFunctor.Obj (State M) :=
  match M.view s with
  | .inl result => .inr ⟨.inl (.inr (finalIndex result)), fun _ => done M result marks⟩
  | .inr ⟨.inl (.inl n), next⟩ => .inr ⟨.inl (.inl n), fun r => ready M (next r) marks⟩
  | .inr ⟨.inl (.inr t), next⟩ => .inr ⟨.inl (.inr t), fun h => ready M (next h) (markHash :: marks)⟩
  | .inr ⟨.inr m, _⟩ => .inr ⟨.inl (.inr m.1), fun (h : G₁) => gotHash M s h marks⟩

/-- One step of the wrapper. -/
def step : State M → Out ⊕ (Spec F K G₁ randomBound).toPFunctor.Obj (State M)
  | .inl (s, marks) => readyStep M finalIndex s marks
  | .inr (.inl (s, h, marks)) =>
    match M.view s with
    | .inr ⟨.inr m, next⟩ =>
      .inr ⟨.inr m, fun (σ : G₁) => ready M (next (σ + correction m • h)) (markSign correction m :: marks)⟩
    | _ => readyStep M finalIndex s marks
  | .inr (.inr (result, marks)) => .inl (fin result marks)

/-! ### Steps in terms of the inner view -/
section Views
variable {s : M.State} {marks : List (Mark F)}

theorem readyStep_inl {result : In} (h : M.view s = .inl result) :
    readyStep (Out := Out) M finalIndex s marks =
      .inr ⟨.inl (.inr (finalIndex result)), fun _ => done M result marks⟩ := by
  unfold readyStep; rw [h]
theorem readyStep_random {n : Fin (randomBound + 1)}
    {next : (Spec F K G₁ randomBound).Range (.inl (.inl n)) → M.State}
    (h : M.view s = .inr ⟨.inl (.inl n), next⟩) :
    readyStep (Out := Out) M finalIndex s marks = .inr ⟨.inl (.inl n), fun r => ready M (next r) marks⟩ := by
  unfold readyStep; rw [h]
theorem readyStep_hash {t : K} {next : (Spec F K G₁ randomBound).Range (.inl (.inr t)) → M.State}
    (h : M.view s = .inr ⟨.inl (.inr t), next⟩) :
    readyStep (Out := Out) M finalIndex s marks =
      .inr ⟨.inl (.inr t), fun point => ready M (next point) (markHash :: marks)⟩ := by
  unfold readyStep; rw [h]
theorem readyStep_sign {m : K × F} {next : (Spec F K G₁ randomBound).Range (.inr m) → M.State}
    (h : M.view s = .inr ⟨.inr m, next⟩) :
    readyStep (Out := Out) M finalIndex s marks =
      .inr ⟨.inl (.inr m.1), fun (point : G₁) => gotHash M s point marks⟩ := by
  unfold readyStep; rw [h]

theorem step_ready : step M correction finalIndex fin (ready M s marks) = readyStep M finalIndex s marks := rfl
theorem step_gotHash {m : K × F} {next : (Spec F K G₁ randomBound).Range (.inr m) → M.State}
    (h : M.view s = .inr ⟨.inr m, next⟩) (point : G₁) :
    step M correction finalIndex fin (gotHash M s point marks) =
      .inr ⟨.inr m, fun (σ : G₁) => ready M (next (σ + correction m • point)) (markSign correction m :: marks)⟩ := by
  dsimp only [step, gotHash]; rw [h]
theorem step_done (result : In) : step M correction finalIndex fin (done M result marks) = .inl (fin result marks) := rfl
end Views

variable {U : Type} (split : U → α)

/-- The wrapped machine. Reducible, so its states are visibly sums of pairs. -/
@[reducible] def machine : DynComputation (Spec F K G₁ randomBound).toPFunctor U Out :=
  DynComputation.ofStep (step M correction finalIndex fin) fun u => ready M (M.init (split u)) []

/-! ## The wrapper program -/

/-- Forward randomness and hashes, marking hashes; before a signing request hash its period, and
add `correction m • H(t)` to the signer's reply. -/
def translator : QueryImpl (Spec F K G₁ randomBound)
    (StateT (List (Mark F)) (OracleComp (Spec F K G₁ randomBound)))
  | .inl (.inl n) => StateT.mk fun marks => do
      let u ← (liftM ((Spec F K G₁ randomBound).query (.inl (.inl n))) :
        OracleComp (Spec F K G₁ randomBound) (Fin (n.val + 1)))
      pure (u, marks)
  | .inl (.inr t) => StateT.mk fun marks => do
      let point ← (liftM ((Spec F K G₁ randomBound).query (.inl (.inr t))) :
        OracleComp (Spec F K G₁ randomBound) G₁)
      pure (point, markHash :: marks)
  | .inr m => StateT.mk fun marks => do
      let point : G₁ ← (liftM ((Spec F K G₁ randomBound).query (.inl (.inr m.1))) :
        OracleComp (Spec F K G₁ randomBound) G₁)
      let signature : G₁ ← (liftM ((Spec F K G₁ randomBound).query (.inr m)) :
        OracleComp (Spec F K G₁ randomBound) G₁)
      pure (signature + correction m • point, markSign correction m :: marks)

/-- The wrapper program around an inner residual program `P` with marks `marks` recorded. -/
def translate (P : OracleComp (Spec F K G₁ randomBound) In) (marks : List (Mark F)) :
    OracleComp (Spec F K G₁ randomBound) Out := do
  let (result, marks) ← (simulateQ (translator correction) P).run marks
  let _ ← (liftM ((Spec F K G₁ randomBound).query (.inl (.inr (finalIndex result)))) :
    OracleComp (Spec F K G₁ randomBound) G₁)
  pure (fin result marks)

theorem translate_pure (result : In) (marks : List (Mark F)) :
    translate correction finalIndex fin (pure result) marks =
      OracleComp.queryBind (spec := Spec F K G₁ randomBound) (.inl (.inr (finalIndex result)))
        fun _ => pure (fin result marks) := rfl

theorem translate_random (n : Fin (randomBound + 1))
    (k : (Spec F K G₁ randomBound).Range (.inl (.inl n)) → OracleComp (Spec F K G₁ randomBound) In)
    (marks : List (Mark F)) :
    translate correction finalIndex fin
        (OracleComp.queryBind (spec := Spec F K G₁ randomBound) (.inl (.inl n)) k) marks =
      OracleComp.queryBind (spec := Spec F K G₁ randomBound) (.inl (.inl n))
        fun r => translate correction finalIndex fin (k r) marks := rfl

theorem translate_hash (t : K) (k : (Spec F K G₁ randomBound).Range (.inl (.inr t)) → OracleComp (Spec F K G₁ randomBound) In)
    (marks : List (Mark F)) :
    translate correction finalIndex fin
        (OracleComp.queryBind (spec := Spec F K G₁ randomBound) (.inl (.inr t)) k) marks =
      OracleComp.queryBind (spec := Spec F K G₁ randomBound) (.inl (.inr t))
        fun h => translate correction finalIndex fin (k h) (markHash :: marks) := rfl

theorem translate_sign (m : K × F) (k : (Spec F K G₁ randomBound).Range (.inr m) → OracleComp (Spec F K G₁ randomBound) In)
    (marks : List (Mark F)) :
    translate correction finalIndex fin
        (OracleComp.queryBind (spec := Spec F K G₁ randomBound) (.inr m) k) marks =
      OracleComp.queryBind (spec := Spec F K G₁ randomBound) (.inl (.inr m.1)) fun (h : G₁) =>
        OracleComp.queryBind (spec := Spec F K G₁ randomBound) (.inr m) fun (σ : G₁) =>
          translate correction finalIndex fin (k (σ + correction m • h)) (markSign correction m :: marks) := rfl

/-! ## Implementation -/

/-- Machine states against residual wrapper programs. -/
def Rel : State M → OracleComp (Spec F K G₁ randomBound) Out → Prop
  | .inl (s, marks), Q => ∃ P : OracleComp (Spec F K G₁ randomBound) In,
      M.toDynSystem.behavior s = FreeM.toResumption P ∧ Q = translate correction finalIndex fin P marks
  | .inr (.inl (s, h, marks)), Q => ∃ (m : K × F)
      (k : (Spec F K G₁ randomBound).Range (.inr m) → OracleComp (Spec F K G₁ randomBound) In),
      M.toDynSystem.behavior s =
        FreeM.toResumption (OracleComp.queryBind (spec := Spec F K G₁ randomBound) (.inr m) k) ∧
      Q = OracleComp.queryBind (spec := Spec F K G₁ randomBound) (.inr m) fun (σ : G₁) =>
        translate correction finalIndex fin (k (σ + correction m • h)) (markSign correction m :: marks)
  | .inr (.inr (result, marks)), Q => Q = pure (fin result marks)

theorem steps : Model.Machine.Steps (machine M correction finalIndex fin split) (Rel M correction finalIndex fin) := by
  rintro core Q hR
  rcases core with ⟨s, marks⟩ | ⟨s, h, marks⟩ | ⟨result, marks⟩
  · obtain ⟨P, hb, rfl⟩ := hR
    rcases hv : M.view s with result | ⟨(n | t) | m, next⟩
    · obtain rfl := Model.Machine.eq_pure_of_view_inl M hb hv
      refine Or.inr ⟨.inl (.inr (finalIndex result)), fun _ => done M result marks, _, ?_,
        translate_pure _ _ _ _ _, fun _ => rfl⟩
      simp [machine, step, readyStep, hv]
    · obtain ⟨k, rfl, hk⟩ := Model.Machine.exists_liftBind_of_view_inr M hb hv
      refine Or.inr ⟨.inl (.inl n), fun r => ready M (next r) marks, _, ?_,
        translate_random _ _ _ _ _ _, fun r => ⟨k r, hk r, rfl⟩⟩
      simp [machine, step, readyStep, hv]
    · obtain ⟨k, rfl, hk⟩ := Model.Machine.exists_liftBind_of_view_inr M hb hv
      refine Or.inr ⟨.inl (.inr t), fun point => ready M (next point) (markHash :: marks), _, ?_,
        translate_hash _ _ _ _ _ _, fun point => ⟨k point, hk point, rfl⟩⟩
      simp [machine, step, readyStep, hv]
    · obtain ⟨k, rfl, hk⟩ := Model.Machine.exists_liftBind_of_view_inr M hb hv
      refine Or.inr ⟨.inl (.inr m.1), fun point => gotHash M s point marks, _, ?_,
        translate_sign _ _ _ _ _ _, fun point => ⟨m, k, hb, rfl⟩⟩
      simp [machine, step, readyStep, hv]
  · obtain ⟨m, k, hb, rfl⟩ := hR
    obtain ⟨next, hv, hk⟩ := Model.Machine.view_of_behavior_liftBind M hb
    refine Or.inr ⟨.inr m, fun (σ : G₁) => ready M (next (σ + correction m • h)) (markSign correction m :: marks), _, ?_,
      rfl, fun (σ : G₁) => ⟨k (σ + correction m • h), hk _, rfl⟩⟩
    simp [machine, step, hv]
  · obtain rfl := hR
    exact Or.inl ⟨fin result marks, by simp [machine, step], rfl⟩

theorem implements (inner : α → OracleComp (Spec F K G₁ randomBound) In) (hM : M.Implements inner) :
    (machine M correction finalIndex fin split).Implements
      fun u => translate correction finalIndex fin (inner (split u)) [] :=
  Model.Machine.implements_of_steps _ (steps M correction finalIndex fin split) _ fun u =>
    ⟨inner (split u), hM (split u), rfl⟩

/-! ## Query budget -/

/-- Signing requests. -/
abbrev isSign (request : GeneralRequest K (K × F) randomBound) : Prop := request.isRight = true

theorem isQueryBoundP_queryBind_iff {ι : Type} {spec : OracleSpec ι} {β : Type} (p : ι → Prop) [DecidablePred p]
    (t : ι) (k : spec.Range t → OracleComp spec β) (n : ℕ) :
    IsQueryBoundP (OracleComp.queryBind t k) p n ↔
      (¬ p t ∨ 0 < n) ∧ ∀ u, IsQueryBoundP (k u) p (if p t then n - 1 else n) := Iff.rfl

/-- The wrapper's depth: the inner depth, one extra hash per signing request, the final hash. -/
theorem translate_isTotalRollBound (P : OracleComp (Spec F K G₁ randomBound) In)
    (marks : List (Mark F)) (n signs : ℕ) (hn : P.IsTotalRollBound n)
    (hs : IsQueryBoundP P isSign signs) :
    (translate correction finalIndex fin P marks).IsTotalRollBound (n + signs + 1) := by
  induction P generalizing marks n signs with
  | pure result =>
    change FreeM.IsTotalRollBound (translate correction finalIndex fin (pure result) marks) _
    rw [translate_pure, FreeM.isTotalRollBound_liftBind_iff]
    exact ⟨by omega, fun _ => FreeM.isTotalRollBound_pure _ _⟩
  | queryBind t k ih =>
    rw [FreeM.isTotalRollBound_liftBind_iff] at hn
    rw [isQueryBoundP_queryBind_iff] at hs
    rcases t with (r | t) | m
    · rw [translate_random, FreeM.isTotalRollBound_liftBind_iff]
      refine ⟨by omega, fun r => (ih r marks (n - 1) signs (hn.2 r) (by simpa [isSign] using hs.2 r)).mono (by omega)⟩
    · rw [translate_hash, FreeM.isTotalRollBound_liftBind_iff]
      refine ⟨by omega, fun h => (ih h _ (n - 1) signs (hn.2 h) (by simpa [isSign] using hs.2 h)).mono (by omega)⟩
    · have hsigns : 0 < signs := by simpa [isSign] using hs.1
      rw [translate_sign, FreeM.isTotalRollBound_liftBind_iff]
      refine ⟨by omega, fun h => ?_⟩
      rw [FreeM.isTotalRollBound_liftBind_iff]
      refine ⟨by omega, fun σ => (ih _ _ (n - 1) (signs - 1) (hn.2 _) (by simpa [isSign] using hs.2 _)).mono (by omega)⟩

/-- Bounded implementation of the wrapper from bounded implementation of the inner attacker
and a bound on its signing requests. -/
theorem implementsWithin (inner : α → OracleComp (Spec F K G₁ randomBound) In) (n signs : ℕ)
    (hM : M.ImplementsWithin inner n) (hs : ∀ a, IsQueryBoundP (inner a) isSign signs) :
    (machine M correction finalIndex fin split).ImplementsWithin
      (fun u => translate correction finalIndex fin (inner (split u)) []) (n + signs + 1) := by
  rw [implementsWithin_iff_implements_and_bound] at hM ⊢
  exact ⟨implements M correction finalIndex fin split inner hM.1,
    fun u => translate_isTotalRollBound correction finalIndex fin _ [] n signs (hM.2 _) (hs _)⟩

end Signatures.Runtime.SyncWrapGeneral
