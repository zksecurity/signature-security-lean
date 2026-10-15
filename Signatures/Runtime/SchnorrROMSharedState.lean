import Signatures.Runtime.SchnorrROMListPass
import Signatures.Runtime.SchnorrRawTape

/-! Interpret the established finite-list ROM pass over one shared raw tape.
The product rearrangement is a proof-side state relation; native adapters have
separate code, description and runtime obligations. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.ListROM.Shared

abbrev Tape (F : Type) := List (TapeCell F) × List (TapeCell F)
abbrev Caches (F G M : Type) := (G × G) × List ((M × G) × F) × List ((M × G) × F)
abbrev Store (F G M : Type) := Caches F G M × Tape F

variable {F A B : Type} [Field F] [SampleableType F]

def tapeRun (main : OracleComp (expandedSpec F) A) (tape : Tape F) : ProbComp (A × Tape F) :=
  (fun p => (p.1, p.2.saved, p.2.remaining)) <$>
    simulateQ _root_.Schnorr.LazyROM.sample ((simulateQ RawTape.oracle main).run ⟨tape.1, tape.2⟩)

theorem tapeRun_pure (a : A) (tape : Tape F) : tapeRun (pure a) tape = pure (a, tape) := by
  simp [tapeRun]

theorem tapeRun_bind (main : OracleComp (expandedSpec F) A) (next : A → OracleComp (expandedSpec F) B)
    (tape : Tape F) :
    tapeRun (main >>= next) tape = (tapeRun main tape >>= fun p => tapeRun (next p.1) p.2) := by
  simp only [tapeRun, simulateQ_bind, StateT.run_bind, map_bind, bind_map_left]

theorem tapeRun_map (f : A → B) (main : OracleComp (expandedSpec F) A) (tape : Tape F) :
    tapeRun (f <$> main) tape = (fun p => (f p.1, p.2)) <$> tapeRun main tape := by
  simp only [map_eq_bind_pure_comp, tapeRun_bind, Function.comp_apply, tapeRun_pure]
  rfl

variable {G M : Type}

def interpret (main : StateT (Caches F G M) (OracleComp (expandedSpec F)) A) :
    StateT (Store F G M) ProbComp A := fun saved =>
  (fun p => (p.1.1, p.1.2, p.2)) <$> tapeRun (main.run saved.1) saved.2

theorem interpret_pure (a : A) (saved : Store F G M) :
    (interpret (pure a)).run saved = pure (a, saved) := by
  change (fun p => (p.1.1, p.1.2, p.2)) <$> tapeRun (pure (a, saved.1)) saved.2 = _
  rw [tapeRun_pure]
  rfl

theorem interpret_bind (main : StateT (Caches F G M) (OracleComp (expandedSpec F)) A)
    (next : A → StateT (Caches F G M) (OracleComp (expandedSpec F)) B) :
    interpret (main >>= next) = (interpret main >>= fun a => interpret (next a)) := by
  funext saved
  change (interpret (main >>= next)).run saved =
    (interpret main >>= fun a => interpret (next a)).run saved
  rw [StateT.run_bind]
  change (fun p => (p.1.1, p.1.2, p.2)) <$> tapeRun ((main >>= next).run saved.1) saved.2 = _
  rw [StateT.run_bind, tapeRun_bind]
  simp only [interpret, StateT.run, map_bind, bind_map_left]

theorem interpret_map (f : A → B) (main : StateT (Caches F G M) (OracleComp (expandedSpec F)) A)
    (saved : Store F G M) :
    (interpret (f <$> main)).run saved = (fun p => (f p.1, p.2)) <$> (interpret main).run saved := by
  change (fun p => (p.1.1, p.1.2, p.2)) <$> tapeRun ((f <$> main).run saved.1) saved.2 = _
  rw [StateT.run_map, tapeRun_map]
  simp only [interpret, StateT.run, Functor.map_map]

theorem interpret_simulate {I : Type} {spec : OracleSpec I}
    (H : QueryImpl spec (StateT (Caches F G M) (OracleComp (expandedSpec F))))
    (main : OracleComp spec A) :
    interpret (simulateQ H main) = simulateQ (fun i => interpret (H i)) main := by
  induction main using OracleComp.inductionOn with
  | pure value =>
      funext saved
      exact interpret_pure value saved
  | query_bind i next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, interpret_bind, ih]

variable [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  {G₂ K : Type} [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem hash_run (k : M × G) (saved : Store F G M) :
    (interpret (handler (G₂ := G₂) (K := K) (.inl (.inr k)))).run saved =
      match cacheMap saved.1.2.1 k with
      | some c => pure (c, saved)
      | none =>
        match cacheMap saved.1.2.2 k with
        | some c => pure (c, (saved.1.1, (k, c) :: saved.1.2.1, saved.1.2.2), saved.2)
        | none => (fun p => (p.1, (saved.1.1, (k, p.1) :: saved.1.2.1,
            (k, p.1) :: saved.1.2.2), p.2)) <$>
              tapeRun (liftM ((expandedSpec F).query (.inr ()))) saved.2 := by
  rcases saved with ⟨⟨⟨g, pk⟩, managed, live⟩, tape⟩
  change (fun p => (p.1.1, p.1.2, p.2)) <$>
    tapeRun (simulateQ (Replay.expandPrivate privateImpl)
      ((taggedHash.denote (arithmetic F G G₂ K M PrimitiveCosts.unit) taggedSemantics (k, ())).run
        ((g, pk), managed, live))) tape = _
  rw [taggedHash_denote]
  cases hm : cacheMap managed k <;> cases hl : cacheMap live k <;>
    simp [simulateQ_map, simulateQ_pure, Replay.expandPrivate,
      tapeRun_pure, tapeRun_map, Functor.map_map]

theorem finalHash_run (k : M × G) (saved : Store F G M) :
    (interpret (finalHash (G₂ := G₂) (K := K) k)).run saved =
      match cacheMap saved.1.2.2 k with
      | some c => pure (c, saved)
      | none => (fun p => (p.1, (saved.1.1, saved.1.2.1, (k, p.1) :: saved.1.2.2), p.2)) <$>
          tapeRun (liftM ((expandedSpec F).query (.inr ()))) saved.2 := by
  rcases saved with ⟨⟨⟨g, pk⟩, managed, live⟩, tape⟩
  change (fun p => (p.1.1, p.1.2, p.2)) <$>
    tapeRun (simulateQ (Replay.expandPrivate privateImpl)
      ((taggedFinalHash.denote (arithmetic F G G₂ K M PrimitiveCosts.unit) taggedSemantics (k, ())).run
        ((g, pk), managed, live))) tape = _
  rw [taggedFinalHash_denote]
  cases hl : cacheMap live k <;>
    simp [simulateQ_map, simulateQ_pure, Replay.expandPrivate,
      tapeRun_pure, tapeRun_map, Functor.map_map]

theorem signing_run (msg : M) (saved : Store F G M) :
    (interpret (handler (G₂ := G₂) (K := K) (.inr msg))).run saved = (do
      let first ← tapeRun (privateImpl (.inr ())) saved.2
      let second ← tapeRun (privateImpl (.inr ())) first.2
      let commitment := second.1 • saved.1.1.1 - first.1 • saved.1.1.2
      let updated := (cacheProgram (val := scalar) hashEq).denote (arithmetic F G G₂ K M PrimitiveCosts.unit)
        ((msg, commitment), first.1, saved.1.2.1, ())
      pure ((commitment, second.1), (saved.1.1, updated, saved.1.2.2), second.2)) := by
  rcases saved with ⟨⟨⟨g, pk⟩, managed, live⟩, tape⟩
  change (fun p => (p.1.1, p.1.2, p.2)) <$>
    tapeRun (simulateQ (Replay.expandPrivate privateImpl)
      ((taggedSign.denote (arithmetic F G G₂ K M PrimitiveCosts.unit) taggedSemantics (msg, ())).run
        ((g, pk), managed, live))) tape = _
  rw [taggedSign_denote]
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_spec_query, Replay.expandPrivate,
    tapeRun_bind, tapeRun_pure, map_bind, map_pure, Expr.run_value]
  rfl

end Signatures.Runtime.Schnorr.ListROM.Shared
