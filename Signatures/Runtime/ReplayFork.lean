import Signatures.Runtime.Replay

/-! A transcript-only implementation of contextual forking. It re-executes from the
root, retaining the answers strictly before the selected query. This file proves
semantic equivalence; ReplayScan and SchnorrForkBudget supply the compiled scan costs. -/

open OracleComp OracleSpec
open PFunctor.FreeM (Cursor)

namespace Signatures.Runtime.Replay

variable {I A : Type} {spec : OracleSpec.{0, 0} I} [DecidableEq I]

attribute [local implicit_reducible] FreeMonoid PFunctor.Idx

omit [DecidableEq I] in
private theorem free_map {B : Type} (f : A → B) (x : OracleComp spec A) :
    PFunctor.FreeM.map f x = f <$> x := rfl

omit [DecidableEq I] in
private theorem free_bind {B : Type} (x : OracleComp spec A) (f : A → OracleComp spec B) :
    PFunctor.FreeM.bind x f = x >>= f := rfl

theorem rerun_log_completion {main : OracleComp spec A} {target : I} {n : Nat}
    (occ : Cursor.Occurrence target main n) :
    rerun main.withQueryLog occ.before =
      (fun c : occ.Completion => pathLogResult main c.path) <$> occ.complete := by
  rw [rerun_log_before]
  change _ = (fun c : occ.Completion => pathLogResult main c.path) <$>
    ((spec.query target : OracleComp spec _) >>= fun answer =>
      (fun suffix => Cursor.Occurrence.Completion.mk answer suffix) <$>
        PFunctor.FreeM.withPath (occ.resume answer))
  simp only [map_bind, Functor.map_map]
  congr 1
  funext answer
  rw [← map_pathLogResult_withPath]
  simp only [free_map, bind_pure_comp, Functor.map_map]
  congr 1
  funext suffix
  simp [pathLogResult, Cursor.Occurrence.Completion.path,
    Cursor.Occurrence.trace_plug, Cursor.Occurrence.output_plug]

/-- Both selectors must choose the same ordinal, and the focused replies must differ.
The second log contains the replayed prefix as well as the independently sampled suffix. -/
def loggedFork [∀ i, DecidableEq (spec.Range i)]
    (main : OracleComp spec A) (budget : I → Nat) (target : I)
    (select : A → Option (Fin (budget target + 1))) : OracleComp spec (Option (A × A)) := do
  let first ← main.withQueryLog
  match select first.1 with
  | none => pure none
  | some index =>
    match splitBefore target index first.2 with
    | none => pure none
    | some (prior, old) =>
      let second ← rerun main.withQueryLog prior
      match splitBefore target index second.2 with
      | none => pure none
      | some (_, fresh) =>
        pure (if old = fresh then none
          else if select second.1 = some index then some (first.1, second.1) else none)

theorem loggedFork_eq_contextFork [∀ i, DecidableEq (spec.Range i)]
    (main : OracleComp spec A) (budget : I → Nat) (target : I)
    (select : A → Option (Fin (budget target + 1))) :
    loggedFork main budget target select = contextFork main budget target select := by
  have hlog : pathLogResult main <$> PFunctor.FreeM.withPath main = main.withQueryLog :=
    map_pathLogResult_withPath main
  unfold loggedFork contextFork contextForkWitness
  rw [Cursor.filterMapLocateAndForkSelected_eq_filterMapLocateAndForkBy,
    Cursor.filterMapLocateAndForkBy_eq_bind_complete]
  conv_lhs => rw [← map_pathLogResult_withPath main]
  simp only [free_map, free_bind, bind_map_left, map_bind]
  congr 1
  funext path
  change (match select (PFunctor.FreeM.output main path) with
    | none => _
    | some index => _) = _
  cases hs : select (PFunctor.FreeM.output main path) with
  | none => simp
  | some index =>
    dsimp only
    rw [splitBefore_trace]
    cases hl : Cursor.locateAt? target main path index with
    | none => simp
    | some located =>
      simp only [Option.map_some]
      rw [hlog, rerun_log_completion]
      simp only [bind_map_left, Functor.map_map]
      conv_rhs => rw [map_eq_bind_pure_comp]
      congr 1
      funext second
      have hsplit := splitBefore_before located.occurrence second.answer
        (PFunctor.FreeM.Path.trace (located.occurrence.resume second.answer) second.suffix)
      have hfirst : PFunctor.FreeM.output (located.occurrence.resume located.completion.answer)
          located.completion.suffix = PFunctor.FreeM.output main path := by
        simpa only [Cursor.Occurrence.Completion.path, Cursor.Occurrence.output_plug] using
          congrArg (PFunctor.FreeM.output main) located.path_eq
      simp only [Cursor.Occurrence.Completion.path,
        Cursor.Occurrence.trace_plug, hsplit]
      simp [acceptContextForkWitness, classifyForkView,
        Cursor.ForkView.firstPath, Cursor.ForkView.secondPath,
        Cursor.ForkView.firstAnswer, Cursor.ForkView.secondAnswer,
        hfirst, hs, Cursor.SelectedForkView.outputs,
        Cursor.Occurrence.Completion.path]
      split <;> split <;> simp_all

omit [DecidableEq I] in
theorem withQueryLog_map {B : Type} (f : A → B) (main : OracleComp spec A) :
    (f <$> main).withQueryLog = Prod.map f id <$> main.withQueryLog := by
  rw [map_eq_bind_pure_comp, withQueryLog_bind]
  simp only [Function.comp_def, withQueryLog_pure, map_pure, Prod.map,
    id_eq, List.append_nil, bind_pure_comp]
  rfl

/-- Changing only the recorded result commutes with replay and fork selection. -/
theorem contextFork_map [∀ i, DecidableEq (spec.Range i)] {B : Type}
    (f : A → B) (main : OracleComp spec A) (budget : I → Nat) (target : I)
    (select : B → Option (Fin (budget target + 1))) :
    contextFork (f <$> main) budget target select =
      Option.map (Prod.map f f) <$> contextFork main budget target (select ∘ f) := by
  rw [← loggedFork_eq_contextFork, ← loggedFork_eq_contextFork]
  unfold loggedFork
  rw [withQueryLog_map]
  simp only [bind_map_left, map_bind, Function.comp_def]
  congr 1
  funext first
  dsimp only [Prod.map, id]
  cases select (f first.1) with
  | none => simp
  | some index =>
    dsimp only
    cases splitBefore target index first.2 with
    | none => simp
    | some prior =>
      dsimp only
      rw [rerun_map]
      simp only [bind_map_left, map_bind]
      congr 1
      funext second
      dsimp only [Prod.map, id]
      cases splitBefore target index second.2 with
      | none => simp
      | some later =>
        dsimp only
        by_cases ha : prior.2 = later.2 <;>
          by_cases hb : select (f second.1) = some index <;> simp [ha, hb]

theorem contextFork_outputs [∀ i, DecidableEq (spec.Range i)]
    (main : OracleComp spec A) (budget : I → Nat) (target : I)
    (select : A → Option (Fin (budget target + 1))) {first second : A}
    (h : some (first, second) ∈ support (contextFork main budget target select)) :
    first ∈ support main ∧ second ∈ support main := by
  obtain ⟨path, index, located, later, _, _, _, _, _, rfl, rfl⟩ :=
    contextFork_success main budget target select h
  rw [PFunctor.FreeM.support_eq_range_output]
  exact ⟨⟨path, rfl⟩, ⟨later.path, rfl⟩⟩

end Signatures.Runtime.Replay
