import Proofs.Runtime.SchnorrRandomness

/-! Semantic refinement for the machine's encoded, indexed replay tape. Equality
with typed replay is asserted on recorded prefixes, not on arbitrary malformed tapes. -/

open OracleComp OracleSpec
open PFunctor.FreeM (Cursor)

namespace Signatures.Runtime.Schnorr

variable {F A : Type} [Zero F]

abbrev TapeCell (F : Type) := Nat × F × Nat
abbrev TapeState (F : Type) := Nat × Nat × List (TapeCell F) × List (TapeCell F)

def encodeReply : (i : (replaySpec F).Domain) → (replaySpec F).Range i → TapeCell F
  | .inl (.inl n), x => (n + 2, 0, x.val)
  | .inl (.inr ()), x => (0, x, 0)
  | .inr (), x => (1, x, 0)

def decodeReply : (i : (replaySpec F).Domain) → TapeCell F → (replaySpec F).Range i
  | .inl (.inl n), x => ⟨x.2.2 % (n + 1), Nat.mod_lt _ (Nat.zero_lt_succ n)⟩
  | .inl (.inr ()), x => x.2.1
  | .inr (), x => x.2.1

def encodeTape (tape : Replay.Tape (replaySpec F)) : List (TapeCell F) :=
  tape.map (fun p => encodeReply p.1 p.2)

private theorem encodeTape_cons (i : (replaySpec F).Domain) (answer : (replaySpec F).Range i)
    (rest : Replay.Tape (replaySpec F)) :
    encodeTape (⟨i, answer⟩ :: rest) = encodeReply i answer :: encodeTape rest := rfl

theorem decode_encode (i : (replaySpec F).Domain) (answer : (replaySpec F).Range i) :
    decodeReply i (encodeReply i answer) = answer := by
  cases i with
  | inr u => cases u; rfl
  | inl j =>
    cases j with
    | inr u => cases u; rfl
    | inl n => apply Fin.ext; exact Nat.mod_eq_of_lt answer.isLt

def indexedTapeImpl : QueryImpl (replaySpec F) (StateT (TapeState F) (OracleComp (replaySpec F))) :=
  fun i s =>
    (fun answer => (answer, (s.1 + 1, s.2.1, s.2.2.1,
      encodeReply i answer :: s.2.2.2))) <$>
      (if s.1 < s.2.1 then pure (decodeReply i ((s.2.2.1[s.1]?).getD (0, 0, 0)))
       else (liftM ((replaySpec F).query i) : OracleComp (replaySpec F) _))

def indexedRun (main : OracleComp (replaySpec F) A) (s : TapeState F) :
    OracleComp (replaySpec F) (A × TapeState F) := (simulateQ indexedTapeImpl main).run s

theorem indexedRun_pure (x : A) (s : TapeState F) : indexedRun (pure x) s = pure (x, s) := rfl

theorem indexedRun_bind {B : Type} (main : OracleComp (replaySpec F) A)
    (next : A → OracleComp (replaySpec F) B) (s : TapeState F) :
    indexedRun (main >>= next) s = (do
      let p ← indexedRun main s
      indexedRun (next p.1) p.2) := by
  simp [indexedRun, StateT.run_bind]

theorem indexedRun_queryBind (i : (replaySpec F).Domain)
    (next : (replaySpec F).Range i → OracleComp (replaySpec F) A) (s : TapeState F) :
    indexedRun (OracleComp.queryBind i next) s = (do
      let p ← indexedTapeImpl i s
      indexedRun (next p.1) p.2) := by
  change ((indexedTapeImpl i >>= fun answer => simulateQ indexedTapeImpl (next answer)).run s) = _
  rw [StateT.run_bind]
  rfl

theorem indexedTapeImpl_hit (i : (replaySpec F).Domain) (answer : (replaySpec F).Range i)
    (prior rest events : List (TapeCell F)) :
    indexedTapeImpl i (prior.length, (prior ++ encodeReply i answer :: rest).length,
      prior ++ encodeReply i answer :: rest, events) =
        pure (answer, (prior.length + 1, (prior ++ encodeReply i answer :: rest).length,
          prior ++ encodeReply i answer :: rest, encodeReply i answer :: events)) := by
  simp [indexedTapeImpl, decode_encode]

attribute [local implicit_reducible] FreeMonoid PFunctor.Idx

omit [Zero F] in
private theorem queryBind_bind (i : (replaySpec F).Domain)
    (next : (replaySpec F).Range i → OracleComp (replaySpec F) A) :
    OracleComp.queryBind i next = ((replaySpec F).query i : OracleComp (replaySpec F) _) >>= next := rfl

/-- Once the prefix ends, all later draws are fresh and the complete suffix is logged.
This equality also accounts for the cursor and reverse chronological event storage. -/
theorem indexedRun_fresh (main : OracleComp (replaySpec F) A)
    (cursor limit : Nat) (tape events : List (TapeCell F)) (h : limit ≤ cursor) :
    indexedRun main (cursor, limit, tape, events) =
      (fun p => (p.1, (cursor + (p.2 : Replay.Tape (replaySpec F)).length, limit, tape,
        (encodeTape p.2).reverse ++ events))) <$> main.withQueryLog := by
  induction main using OracleComp.inductionOn generalizing cursor events with
  | pure value => simp [indexedRun, encodeTape]
  | query_bind i next ih =>
    change indexedRun (OracleComp.queryBind i next) _ =
      (fun p => (p.1, (cursor + (p.2 : Replay.Tape (replaySpec F)).length, limit, tape,
        (encodeTape p.2).reverse ++ events))) <$> (OracleComp.queryBind i next).withQueryLog
    rw [indexedRun_queryBind, Replay.withQueryLog_queryBind]
    simp only [indexedTapeImpl, show ¬ cursor < limit from by omega, ite_false,
      bind_map_left, queryBind_bind, map_bind, Functor.map_map]
    congr 1
    funext answer
    rw [ih answer (cursor + 1) (encodeReply i answer :: events) (by omega)]
    simp only [encodeTape, List.map_cons, List.reverse_cons,
      List.length_cons, List.append_assoc, List.singleton_append]
    congr 1
    funext p
    congr 2
    omega

/-- An indexed tape consumes exactly a typed cursor's prefix. The selected query itself
is not in this prefix, so its answer will be fresh when the residual program starts. -/
theorem indexedRun_spine {main residual : OracleComp (replaySpec F) A}
    (spine : Cursor.Spine main residual) (prior events : List (TapeCell F)) :
    indexedRun main (prior.length, (prior ++ encodeTape spine.trace).length,
      prior ++ encodeTape spine.trace, events) =
      indexedRun residual ((prior ++ encodeTape spine.trace).length,
        (prior ++ encodeTape spine.trace).length, prior ++ encodeTape spine.trace,
        (encodeTape spine.trace).reverse ++ events) := by
  induction spine generalizing prior events with
  | root => simp [encodeTape, Cursor.Spine.trace]
  | @down i next residual answer tail ih =>
    change indexedRun (OracleComp.queryBind i next)
      (prior.length, (prior ++ encodeReply i answer :: encodeTape tail.trace).length,
        prior ++ encodeReply i answer :: encodeTape tail.trace, events) = _
    rw [indexedRun_queryBind, indexedTapeImpl_hit, pure_bind]
    have ht := ih (prior ++ [encodeReply i answer]) (encodeReply i answer :: events)
    simpa [encodeTape, Cursor.Spine.trace, List.append_assoc, List.reverse_cons,
      Nat.add_assoc] using ht

theorem indexedRun_before {main : OracleComp (replaySpec F) A} {target : (replaySpec F).Domain}
    {n : Nat} (occ : Cursor.Occurrence target main n) :
    indexedRun main (0, (encodeTape occ.before).length, encodeTape occ.before, []) =
      (fun p => (p.1,
        ((encodeTape occ.before).length + (p.2 : Replay.Tape (replaySpec F)).length,
          (encodeTape occ.before).length, encodeTape occ.before,
          (encodeTape p.2).reverse ++ (encodeTape occ.before).reverse))) <$>
        (OracleComp.queryBind target occ.resume).withQueryLog := by
  have h := indexedRun_spine occ.toSpine [] []
  simp only [List.length_nil, List.nil_append, List.append_nil] at h
  change indexedRun main (0, (encodeTape occ.before).length, encodeTape occ.before, []) =
    indexedRun (OracleComp.queryBind target occ.resume)
      ((encodeTape occ.before).length, (encodeTape occ.before).length, encodeTape occ.before,
        (encodeTape occ.before).reverse) at h
  rw [h]
  exact indexedRun_fresh _ _ _ _ _ le_rfl

/-- The chronological machine log is exactly the encoding of the complete typed log,
including the forced prefix. No claim is made about adversarially malformed tapes. -/
theorem indexedRun_log_spine {main residual : OracleComp (replaySpec F) A}
    (spine : Cursor.Spine main residual) :
    (fun p => (p.1, p.2.2.2.2.reverse)) <$>
        indexedRun main (0, (encodeTape spine.trace).length, encodeTape spine.trace, []) =
      (fun p => (p.1, encodeTape p.2)) <$> Replay.rerun main.withQueryLog spine.trace := by
  have h := indexedRun_spine spine [] []
  simp only [List.length_nil, List.nil_append, List.append_nil] at h
  rw [h, indexedRun_fresh _ _ _ _ _ le_rfl, Replay.rerun_log_spine]
  simp [Functor.map_map, encodeTape, List.reverse_append]

/-- Locate a live challenge by its ordinal, omitting its answer from the replay prefix.
Private scalar draws and adversary uniform draws remain in the prefix but are not counted. -/
def splitCells : Nat → List (TapeCell F) → Option (List (TapeCell F) × F)
  | _, [] => none
  | n, cell :: rest =>
    if cell.1 = 1 then
      match n with
      | 0 => some ([], cell.2.1)
      | n + 1 => (splitCells n rest).map (fun p => (cell :: p.1, p.2))
    else (splitCells n rest).map (fun p => (cell :: p.1, p.2))

theorem splitCells_encode (n : Nat) (tape : Replay.Tape (replaySpec F)) :
    splitCells n (encodeTape tape) =
      (Replay.splitBefore (Sum.inr ()) n tape).map (fun p => (encodeTape p.1, p.2)) := by
  induction tape generalizing n with
  | nil => rfl
  | cons cell rest ih =>
    rcases cell with ⟨i, answer⟩
    cases i with
    | inr u =>
      cases u
      cases n with
      | zero => rfl
      | succ n =>
        simp only [encodeTape_cons, encodeReply, splitCells, ite_true, Replay.splitBefore,
          dite_true]
        rw [ih]
        simp [Option.map_map, Function.comp_def, encodeTape, encodeReply]
    | inl j =>
      cases j with
      | inl k =>
        have hk : k + 2 ≠ 1 := by omega
        simp only [encodeTape_cons, encodeReply, splitCells, hk, ite_false,
          Replay.splitBefore, Sum.inl_ne_inr, dite_false]
        rw [ih]
        simp [Option.map_map, Function.comp_def, encodeTape, encodeReply]
      | inr u =>
        cases u
        simp only [encodeTape_cons, encodeReply, splitCells, show (0 : Nat) ≠ 1 by omega,
          ite_false, Replay.splitBefore, Sum.inl_ne_inr, dite_false]
        rw [ih]
        simp [Option.map_map, Function.comp_def, encodeTape, encodeReply]

def indexedLoggedRun (main : OracleComp (replaySpec F) A) (tape : List (TapeCell F)) :
    OracleComp (replaySpec F) (A × List (TapeCell F)) :=
  (fun p => (p.1, p.2.2.2.2.reverse)) <$> indexedRun main (0, tape.length, tape, [])

theorem indexedLoggedRun_empty (main : OracleComp (replaySpec F) A) :
    indexedLoggedRun main [] = (fun p => (p.1, encodeTape p.2)) <$> main.withQueryLog := by
  rw [indexedLoggedRun, List.length_nil, indexedRun_fresh _ _ _ _ _ le_rfl]
  simp [Functor.map_map]

theorem indexedLoggedRun_before {main : OracleComp (replaySpec F) A}
    {target : (replaySpec F).Domain} {n : Nat} (occ : Cursor.Occurrence target main n) :
    indexedLoggedRun main (encodeTape occ.before) =
      (fun p => (p.1, encodeTape p.2)) <$> Replay.rerun main.withQueryLog occ.before :=
  indexedRun_log_spine occ.toSpine

/-- The encoded controller's semantic specification. Its scans and list reversal are
not free machine operations; the executable controller must implement and charge them. -/
def indexedFork [DecidableEq F] (main : OracleComp (replaySpec F) A) (qH : Nat)
    (select : A → Option (Fin (qH + 1))) : OracleComp (replaySpec F) (Option (A × A)) := do
  let first ← indexedLoggedRun main []
  match select first.1 with
  | none => pure none
  | some index =>
    match splitCells index first.2 with
    | none => pure none
    | some (prior, old) =>
      let second ← indexedLoggedRun main prior
      match splitCells index second.2 with
      | none => pure none
      | some (_, fresh) =>
        pure (if old = fresh then none
          else if select second.1 = some index then some (first.1, second.1) else none)

omit [Zero F] in
private theorem free_map {B : Type} (f : A → B) (main : OracleComp (replaySpec F) A) :
    PFunctor.FreeM.map f main = f <$> main := rfl

theorem indexedFork_eq_loggedFork [DecidableEq F]
    (main : OracleComp (replaySpec F) A) (qH : Nat)
    (select : A → Option (Fin (qH + 1))) :
    indexedFork main qH select = Replay.loggedFork main (fun _ => qH) (.inr ()) select := by
  unfold indexedFork Replay.loggedFork
  rw [indexedLoggedRun_empty]
  simp only [bind_map_left]
  conv_lhs => lhs; rw [← map_pathLogResult_withPath main]
  conv_rhs => lhs; rw [← map_pathLogResult_withPath main]
  simp only [free_map, bind_map_left]
  congr 1
  funext path
  change (match select (PFunctor.FreeM.output main path) with
    | none => _
    | some index => _) = _
  cases hs : select (PFunctor.FreeM.output main path) with
  | none => rfl
  | some index =>
    dsimp only
    rw [splitCells_encode, Replay.splitBefore_trace]
    cases hl : Cursor.locateAt? (P := (replaySpec F).toPFunctor) (Sum.inr ()) main path index with
    | none => rfl
    | some located =>
      simp only [Option.map_some]
      rw [indexedLoggedRun_before]
      simp only [bind_map_left]
      congr 1
      funext second
      rw [splitCells_encode]
      cases Replay.splitBefore (Sum.inr ()) index second.2 <;> rfl

/-- Indexed replay, after expanding actual private samplers, has the exact joint
distribution of VCVio's contextual fork. This does not assume sampler atomicity. -/
theorem expand_indexedFork [SampleableType F] [DecidableEq F]
    (main : OracleComp (replaySpec F) A) (qH : Nat)
    (select : A → Option (Fin (qH + 1))) :
    simulateQ (Replay.expandPrivate privateImpl) (indexedFork main qH select) =
      contextFork (simulateQ (Replay.expandPrivate privateImpl) main)
        (fun _ => qH) (.inr ()) select := by
  rw [indexedFork_eq_loggedFork]
  exact expand_loggedFork main qH select

end Signatures.Runtime.Schnorr
