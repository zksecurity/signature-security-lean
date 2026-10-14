import VCVio.CryptoFoundations.ReplayFork
import VCVio.OracleComp.SimSemantics.SimulateQ

/-! Replay from the root using a finite recorded prefix. The semantic bridge below
justifies re-executing first-order code instead of storing a Lean continuation.
It is not itself a machine-time certificate. -/

open OracleComp OracleSpec
open PFunctor.FreeM (Cursor)

namespace Signatures.Runtime.Replay

variable {I A : Type} {spec : OracleSpec.{0, 0} I} [DecidableEq I]

abbrev Tape (spec : OracleSpec.{0, 0} I) := List ((i : I) × spec.Range i)

/-- Consume one matching recorded answer. An exhausted or mismatched tape falls back
to the real oracle and discards the remaining tape. A valid prefix never mismatches. -/
def tapeImpl : QueryImpl spec (StateT (Tape spec) (OracleComp spec)) := fun i tape =>
  match tape with
  | [] => (fun answer => (answer, [])) <$> (spec.query i : OracleComp spec _)
  | ⟨j, answer⟩ :: rest =>
    if h : j = i then pure (h ▸ answer, rest)
    else (fun answer => (answer, [])) <$> (spec.query i : OracleComp spec _)

def rerun (main : OracleComp spec A) (tape : Tape spec) : OracleComp spec A :=
  (simulateQ tapeImpl main).run' tape

theorem rerun_queryBind (i : I) (next : spec.Range i → OracleComp spec A) (tape : Tape spec) :
    rerun (OracleComp.queryBind i next) tape =
      (do
        let (answer, rest) ← (tapeImpl i).run tape
        rerun (next answer) rest) := by
  change Prod.fst <$> ((tapeImpl i >>= fun answer => simulateQ tapeImpl (next answer)).run tape) = _
  simp only [StateT.run_bind, map_bind, rerun, StateT.run'_eq]

theorem rerun_empty (main : OracleComp spec A) : rerun main [] = main := by
  induction main using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind i next ih =>
    change rerun (OracleComp.queryBind i next) [] = _
    rw [rerun_queryBind]
    simp [tapeImpl, StateT.run, bind_map_left, ih]

theorem rerun_map {B : Type} (f : A → B) (main : OracleComp spec A) (tape : Tape spec) :
    rerun (f <$> main) tape = f <$> rerun main tape := by
  simp [rerun, StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map]

attribute [local implicit_reducible] FreeMonoid PFunctor.Idx

/-- Re-execution consumes precisely the recorded prefix and then runs the residual
program with fresh oracle replies. This holds for every typed cursor, not only one game. -/
theorem rerun_spine {main residual : OracleComp spec A}
    (spine : Cursor.Spine main residual) : rerun main spine.trace = residual := by
  induction spine with
  | root => exact rerun_empty _
  | @down i next residual answer tail ih =>
    change rerun (OracleComp.queryBind i next) (⟨i, answer⟩ :: tail.trace) = _
    rw [rerun_queryBind]
    simpa [tapeImpl, StateT.run] using ih

/-- At a selected occurrence, replay stops before its answer: that answer is resampled,
as is the suffix, while every earlier oracle reply is retained. -/
theorem rerun_before {main : OracleComp spec A} {target : I} {n : Nat}
    (occ : Cursor.Occurrence target main n) :
    rerun main occ.before = OracleComp.queryBind target occ.resume :=
  rerun_spine occ.toSpine

omit [DecidableEq I] in
theorem withQueryLog_queryBind (i : I) (next : spec.Range i → OracleComp spec A) :
    (OracleComp.queryBind i next).withQueryLog =
      OracleComp.queryBind i (fun answer =>
        (fun p => (p.1, ⟨i, answer⟩ :: p.2)) <$> (next answer).withQueryLog) := by
  change OracleComp.withQueryLog ((spec.query i : OracleComp spec _) >>= next) = _
  simp [withQueryLog_bind, withQueryLog_query, bind_map_left]
  rfl

/-- Logging the replay records the complete second path, including forced prefix replies.
This is a joint transcript equality, stronger than equality of final-output distributions. -/
theorem rerun_log_spine {main residual : OracleComp spec A}
    (spine : Cursor.Spine main residual) :
    rerun main.withQueryLog spine.trace =
      (fun p => (p.1, List.append (spine.trace : Tape spec) (p.2 : Tape spec))) <$>
        residual.withQueryLog := by
  induction spine with
  | root program =>
    change rerun (OracleComp.withQueryLog program) [] = id <$> OracleComp.withQueryLog program
    simpa using
      rerun_empty (OracleComp.withQueryLog program)
  | @down i next residual answer tail ih =>
    change rerun (OracleComp.queryBind i next).withQueryLog
      (⟨i, answer⟩ :: tail.trace) = _
    rw [withQueryLog_queryBind, rerun_queryBind]
    simp only [tapeImpl, StateT.run, dite_true, pure_bind]
    rw [rerun_map, ih]
    simp [Functor.map_map, Cursor.Spine.trace]

/-- Split a recorded path immediately before the selected target occurrence. The focused
answer is kept separately so replay can replace it rather than accidentally reuse it. -/
def splitBefore (target : I) : Nat → Tape spec → Option (Tape spec × spec.Range target)
  | _, [] => none
  | n, (⟨i, answer⟩ :: rest) =>
    if h : i = target then
      match n with
      | 0 => some ([], h ▸ answer)
      | n + 1 => (splitBefore target n rest).map (fun p => (⟨i, answer⟩ :: p.1, p.2))
    else (splitBefore target n rest).map (fun p => (⟨i, answer⟩ :: p.1, p.2))

theorem splitBefore_trace (target : I) (main : OracleComp spec A)
    (path : PFunctor.FreeM.Path main) (n : Nat) :
    splitBefore target n (PFunctor.FreeM.Path.trace main path) =
      (Cursor.locateAt? target main path n).map
        (fun located => (located.occurrence.before, located.completion.answer)) := by
  induction main generalizing n with
  | pure a => rfl
  | queryBind i next ih =>
    rcases path with ⟨answer, suffix⟩
    change splitBefore target n (⟨i, answer⟩ :: PFunctor.FreeM.Path.trace (next answer) suffix) =
      (Cursor.locateAt? (P := spec.toPFunctor) target
        (PFunctor.FreeM.liftBind i next) ⟨answer, suffix⟩ n).map _
    by_cases h : i = target
    · subst i
      cases n with
      | zero => simp [splitBefore, Cursor.locateAt?, Cursor.Located.here,
          Cursor.Occurrence.before, Cursor.Occurrence.toCursor, Cursor.Occurrence.toSpine,
          Cursor.trace, Cursor.Spine.trace]
      | succ n =>
        rw [Cursor.locateAt?_liftBind_same_succ]
        simp only [splitBefore, dite_true]
        rw [ih]
        cases Cursor.locateAt? target (next answer) suffix n <;> rfl
    · rw [Cursor.locateAt?_liftBind_other h]
      simp only [splitBefore, h, dite_false]
      rw [ih]
      cases Cursor.locateAt? target (next answer) suffix n <;> rfl

theorem splitBefore_before {main : OracleComp spec A} {target : I} {n : Nat}
    (occ : Cursor.Occurrence target main n) (answer : spec.Range target) (rest : Tape spec) :
    splitBefore target n (List.append (occ.before : Tape spec) (⟨target, answer⟩ :: rest)) =
      some (occ.before, answer) := by
  induction occ with
  | here => simp [Cursor.Occurrence.before, Cursor.Occurrence.toCursor,
      Cursor.trace, Cursor.Occurrence.toSpine, Cursor.Spine.trace, splitBefore]
  | stepSame prior tail ih =>
    change splitBefore target (_ + 1) (⟨target, prior⟩ :: _) = _
    simp only [splitBefore, dite_true]
    exact congrArg (Option.map (fun p : Tape spec × spec.Range target =>
      (⟨target, prior⟩ :: p.1, p.2))) ih
  | stepOther hne prior tail ih =>
    change splitBefore target _ (⟨_, prior⟩ :: _) = _
    simp only [splitBefore, hne, dite_false]
    exact congrArg (Option.map (fun p : Tape spec × spec.Range target =>
      (⟨_, prior⟩ :: p.1, p.2))) ih

theorem rerun_log_before {main : OracleComp spec A} {target : I} {n : Nat}
    (occ : Cursor.Occurrence target main n) :
    rerun main.withQueryLog occ.before = (do
      let answer ← (spec.query target : OracleComp spec _)
      let p ← OracleComp.withQueryLog (occ.resume answer)
      pure (p.1, List.append (occ.before : Tape spec) (⟨target, answer⟩ :: p.2))) := by
  change rerun main.withQueryLog occ.toSpine.trace = _
  rw [rerun_log_spine occ.toSpine]
  rw [withQueryLog_queryBind]
  change (fun p => (p.1, List.append (occ.before : Tape spec) p.2)) <$>
    ((spec.query target : OracleComp spec _) >>= fun answer =>
      (fun p => (p.1, ⟨target, answer⟩ :: p.2)) <$>
        OracleComp.withQueryLog (occ.resume answer)) = _
  simp only [map_bind, Functor.map_map, bind_pure_comp]

end Signatures.Runtime.Replay
