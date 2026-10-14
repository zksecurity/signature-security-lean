import Signatures.Runtime.ReplayFork
import VCVio.OracleComp.QueryTracking.QueryBound

/-! Semantic fork decomposition for expanding private sampling procedures. This is
proof infrastructure, not a machine instruction or an assumed constant-cost snapshot. -/

open OracleComp OracleSpec
open PFunctor.FreeM (Cursor)

namespace Signatures.Runtime.Replay

variable {I A : Type} {spec : OracleSpec.{0, 0} I} [DecidableEq I]

def previous : Option Nat → Option Nat
  | none | some 0 => none
  | some (n + 1) => some n

/-- Retain the first output and, when a selected occurrence exists, its old answer,
fresh answer, and second output. Acceptance guards are applied separately. -/
def forkKernel (target : I) : (main : OracleComp spec A) → (A → Option Nat) →
    OracleComp spec (A × Option (spec.Range target × spec.Range target × A))
  | .pure x, _ => pure (x, none)
  | .liftBind i next, select =>
    if h : i = target then
      OracleComp.queryBind i fun answer => do
        let first ← forkKernel target (next answer) (fun x => previous (select x))
        if select first.1 = some 0 then
          let fresh ← (spec.query i : OracleComp spec _)
          let second ← next fresh
          pure (first.1, some (h ▸ answer, h ▸ fresh, second))
        else pure first
    else OracleComp.queryBind i fun answer => forkKernel target (next answer) select

theorem forkKernel_pure (target : I) (x : A) (select : A → Option Nat) :
    forkKernel target (pure x : OracleComp spec A) select = pure (x, none) := rfl

theorem forkKernel_other (target i : I) (hne : i ≠ target)
    (next : spec.Range i → OracleComp spec A) (select : A → Option Nat) :
    forkKernel target (OracleComp.queryBind i next) select =
      OracleComp.queryBind i (fun answer => forkKernel target (next answer) select) := by
  simp only [OracleComp.queryBind, forkKernel, hne, dite_false]

theorem forkKernel_target (target : I)
    (next : spec.Range target → OracleComp spec A) (select : A → Option Nat) :
    forkKernel target (OracleComp.queryBind target next) select =
      OracleComp.queryBind target (fun answer => do
        let first ← forkKernel target (next answer) (fun x => previous (select x))
        if select first.1 = some 0 then
          let fresh ← (spec.query target : OracleComp spec _)
          let second ← next fresh
          pure (first.1, some (answer, fresh, second))
        else pure first) := by
  simp only [OracleComp.queryBind, forkKernel, dite_true]

/-- A private procedure may make arbitrarily many non-target queries. Expanding it
before forking preserves its sampled result and the entire subsequent fork law. -/
theorem forkKernel_private_bind {B : Type} (target : I) (draw : OracleComp spec B)
    (hdraw : IsQueryBoundP draw (fun i => i = target) 0)
    (next : B → OracleComp spec A) (select : A → Option Nat) :
    forkKernel target (draw >>= next) select =
      draw >>= fun value => forkKernel target (next value) select := by
  induction draw using OracleComp.inductionOn with
  | pure value => simp
  | query_bind i rest ih =>
    rw [isQueryBoundP_query_bind_iff] at hdraw
    have hne : i ≠ target := by simpa using hdraw.1
    change forkKernel target ((spec.query i : OracleComp spec _) >>= rest >>= next) select = _
    rw [bind_assoc]
    change forkKernel target (OracleComp.queryBind i (fun x => rest x >>= next)) select = _
    rw [forkKernel_other target i hne]
    change ((spec.query i : OracleComp spec _) >>= fun x =>
      forkKernel target (rest x >>= next) select) = _
    rw [bind_assoc]
    congr 1
    funext x
    exact ih x (by simpa [hne] using hdraw.2 x)

attribute [local implicit_reducible] FreeMonoid PFunctor.Idx

/-- The same unguarded fork, presented by a typed first path and occurrence. -/
def kernelPath (target : I) (main : OracleComp spec A) (select : A → Option Nat)
    (path : PFunctor.FreeM.Path main) :
    OracleComp spec (A × Option (spec.Range target × spec.Range target × A)) :=
  let first := PFunctor.FreeM.output main path
  match select first with
  | none => pure (first, none)
  | some index =>
    match Cursor.locateAt? target main path index with
    | none => pure (first, none)
    | some located => do
      let fresh ← (spec.query target : OracleComp spec _)
      let second ← located.occurrence.resume fresh
      pure (first, some (located.completion.answer, fresh, second))

theorem kernelPath_none (target : I) (main : OracleComp spec A) (select : A → Option Nat)
    (path : PFunctor.FreeM.Path main) (h : select (PFunctor.FreeM.output main path) = none) :
    kernelPath target main select path = pure (PFunctor.FreeM.output main path, none) := by
  simp [kernelPath, h]

theorem kernelPath_other (target i : I) (hne : i ≠ target)
    (next : spec.Range i → OracleComp spec A) (select : A → Option Nat)
    (answer : spec.Range i) (path : PFunctor.FreeM.Path (next answer)) :
    kernelPath target (OracleComp.queryBind i next) select ⟨answer, path⟩ =
      kernelPath target (next answer) select path := by
  unfold kernelPath
  dsimp only
  change (match select (PFunctor.FreeM.output (next answer) path) with
    | none => _ | some index => _) = _
  cases hs : select (PFunctor.FreeM.output (next answer) path) with
  | none => rfl
  | some index =>
    dsimp only
    rw [Cursor.locateAt?_liftBind_other hne]
    cases Cursor.locateAt? target (next answer) path index <;> rfl

theorem kernelPath_target_succ (target : I)
    (next : spec.Range target → OracleComp spec A) (select : A → Option Nat)
    (answer : spec.Range target) (path : PFunctor.FreeM.Path (next answer)) (index : Nat)
    (hs : select (PFunctor.FreeM.output (next answer) path) = some (index + 1)) :
    kernelPath target (OracleComp.queryBind target next) select ⟨answer, path⟩ =
      kernelPath target (next answer) (fun x => previous (select x)) path := by
  unfold kernelPath
  change (match select (PFunctor.FreeM.output (next answer) path) with
    | none => _ | some index => _) = _
  simp only [hs, previous]
  rw [Cursor.locateAt?_liftBind_same_succ]
  cases Cursor.locateAt? target (next answer) path index <;> rfl

theorem kernelPath_target_zero (target : I)
    (next : spec.Range target → OracleComp spec A) (select : A → Option Nat)
    (answer : spec.Range target) (path : PFunctor.FreeM.Path (next answer))
    (hs : select (PFunctor.FreeM.output (next answer) path) = some 0) :
    kernelPath target (OracleComp.queryBind target next) select ⟨answer, path⟩ = (do
      let fresh ← (spec.query target : OracleComp spec _)
      let second ← next fresh
      pure (PFunctor.FreeM.output (next answer) path, some (answer, fresh, second))) := by
  unfold kernelPath
  change (match select (PFunctor.FreeM.output (next answer) path) with
    | none => _ | some index => _) = _
  simp only [hs]
  rw [Cursor.locateAt?_liftBind_same_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem forkKernel_eq_path (target : I) (main : OracleComp spec A) (select : A → Option Nat) :
    forkKernel target main select =
      PFunctor.FreeM.withPath main >>= kernelPath target main select := by
  induction main using OracleComp.inductionOn generalizing select with
  | pure value =>
    rw [forkKernel_pure]
    cases hs : select value <;>
      simp [kernelPath, hs]
  | query_bind i next ih =>
    change forkKernel target (OracleComp.queryBind i next) select =
      PFunctor.FreeM.bind (PFunctor.FreeM.withPath (PFunctor.FreeM.liftBind i next))
        (kernelPath target (OracleComp.queryBind i next) select)
    rw [PFunctor.FreeM.withPath_liftBind_bind]
    by_cases h : i = target
    · subst i
      rw [forkKernel_target]
      apply congrArg (OracleComp.queryBind target)
      funext answer
      rw [ih answer, bind_assoc]
      congr 1
      funext path
      cases hs : select (PFunctor.FreeM.output (next answer) path) with
      | none =>
        rw [kernelPath_none target (next answer) _ path (by simp [hs, previous])]
        simp only [pure_bind, hs, reduceCtorEq, ite_false]
        exact (kernelPath_none target (OracleComp.queryBind target next) select
          ⟨answer, path⟩ hs).symm
      | some index =>
        cases index with
        | zero =>
          rw [kernelPath_none target (next answer) _ path (by simp [hs, previous])]
          simp only [pure_bind, hs, ite_true]
          exact (kernelPath_target_zero target next select answer path hs).symm
        | succ index =>
          rw [kernelPath_target_succ target next select answer path index hs]
          unfold kernelPath
          simp only [hs, previous]
          cases Cursor.locateAt? target (next answer) path index <;>
            simp [hs, bind_map_left]
    · rw [forkKernel_other target i h]
      apply congrArg (OracleComp.queryBind i)
      funext answer
      rw [ih answer]
      simp only [kernelPath_other target i h]
      rfl

omit [DecidableEq I] in
private theorem free_map {B : Type} (f : A → B) (x : OracleComp spec A) :
    PFunctor.FreeM.map f x = f <$> x := rfl

omit [DecidableEq I] in
private theorem free_bind {B : Type} (x : OracleComp spec A) (f : A → OracleComp spec B) :
    PFunctor.FreeM.bind x f = x >>= f := rfl

omit [DecidableEq I] in
theorem complete_observe {B : Type} {main : OracleComp spec A} {target : I} {index : Nat}
    (occ : Cursor.Occurrence target main index) (observe : spec.Range target → A → B) :
    (fun c : occ.Completion => observe c.answer (PFunctor.FreeM.output main c.path)) <$>
        occ.complete = (do
      let fresh ← (spec.query target : OracleComp spec _)
      let second ← occ.resume fresh
      pure (observe fresh second)) := by
  change (fun c : occ.Completion => observe c.answer (PFunctor.FreeM.output main c.path)) <$>
    ((spec.query target : OracleComp spec _) >>= fun answer =>
      (fun suffix => Cursor.Occurrence.Completion.mk answer suffix) <$>
        PFunctor.FreeM.withPath (occ.resume answer)) = _
  simp only [map_bind, Functor.map_map, Cursor.Occurrence.Completion.path,
    Cursor.Occurrence.output_plug, bind_pure_comp]
  congr 1
  funext answer
  conv_rhs => rw [← PFunctor.FreeM.map_output_withPath (occ.resume answer)]
  simp only [free_map, Functor.map_map]

def acceptKernel {F : Type} [DecidableEq F] {n : Nat}
    (select : A → Option (Fin n))
    (result : A × Option (F × F × A)) : Option (A × A) :=
  match result.2 with
  | none => none
  | some (old, fresh, second) =>
    if old = fresh then none
    else if select result.1 = select second then some (result.1, second) else none

/-- The decomposition preserves the full accepted fork, not merely each marginal run. -/
theorem forkKernel_eq_contextFork [∀ i, DecidableEq (spec.Range i)]
    (main : OracleComp spec A) (budget : I → Nat) (target : I)
    (select : A → Option (Fin (budget target + 1))) :
    acceptKernel select <$> forkKernel target main (fun x => (select x).map Fin.val) =
      contextFork main budget target select := by
  rw [forkKernel_eq_path]
  unfold contextFork contextForkWitness
  rw [Cursor.filterMapLocateAndForkSelected_eq_filterMapLocateAndForkBy,
    Cursor.filterMapLocateAndForkBy_eq_bind_complete]
  simp only [free_map, free_bind, map_bind]
  congr 1
  funext path
  unfold kernelPath
  cases hs : select (PFunctor.FreeM.output main path) with
  | none => simp [hs, acceptKernel]
  | some index =>
    simp only [hs, Option.map_some]
    cases hl : Cursor.locateAt? target main path index with
    | none => simp [acceptKernel]
    | some located =>
      dsimp only
      rw [← complete_observe located.occurrence]
      simp only [Functor.map_map]
      congr 1
      funext second
      simp [acceptKernel, acceptContextForkWitness, classifyForkView,
        Cursor.ForkView.firstPath, Cursor.ForkView.secondPath,
        Cursor.ForkView.firstAnswer, Cursor.ForkView.secondAnswer,
        located.path_eq, hs, Cursor.SelectedForkView.outputs]
      split <;> split <;> simp_all [eq_comm]

end Signatures.Runtime.Replay
