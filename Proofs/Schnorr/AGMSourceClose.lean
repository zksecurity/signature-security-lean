import Proofs.Schnorr.AGMHonest

/-! Close the original AGM source handler under its lazy random oracle and
project the reduction's extra representation metadata away. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction

namespace Schnorr.AGM.Reduction.Source

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]

abbrev Cache (F G M : Type) := (M × G →ₒ F).QueryCache
abbrev ClosedState (F G M : Type) := Schnorr.AGM.State M × Cache F G M

def erase (s : Reduction.State F G M) : ClosedState F G M :=
  (⟨s.signed, s.malformed⟩, QueryCache.ofFn fun key => (s.cache key).map Entry.challenge)

def impl : QueryImpl (BaseSpec F G M) (StateT (Cache F G M) ProbComp) :=
  unifFwdImpl (M × G →ₒ F) + randomOracle (spec := M × G →ₒ F)

noncomputable def close {A : Type}
    (oa : StateT (Schnorr.AGM.State M) (OracleComp (BaseSpec F G M)) A) :
    StateT (ClosedState F G M) ProbComp A := fun s =>
  (fun p => (p.1.1, (p.1.2, p.2))) <$> (simulateQ impl (oa.run s.1)).run s.2

theorem close_run {A : Type}
    (oa : StateT (Schnorr.AGM.State M) (OracleComp (BaseSpec F G M)) A)
    (s : ClosedState F G M) :
    (close oa).run s =
      (fun p => (p.1.1, (p.1.2, p.2))) <$> (simulateQ impl (oa.run s.1)).run s.2 := rfl

@[simp] theorem close_pure {A : Type} (a : A) :
    close (pure a : StateT (Schnorr.AGM.State M) (OracleComp (BaseSpec F G M)) A) = pure a := by
  funext s
  change (close (pure a)).run s = (pure a : StateT (ClosedState F G M) ProbComp A).run s
  simp only [close_run, StateT.run_pure, simulateQ_pure, map_pure]

theorem close_bind {A B : Type}
    (oa : StateT (Schnorr.AGM.State M) (OracleComp (BaseSpec F G M)) A)
    (next : A → StateT (Schnorr.AGM.State M) (OracleComp (BaseSpec F G M)) B) :
    close (oa >>= next) = close oa >>= fun a => close (next a) := by
  funext s
  change (close (oa >>= next)).run s = (close oa >>= fun a => close (next a)).run s
  simp only [close_run, simulateQ_bind, StateT.run_bind, map_bind,
    bind_map_left]

theorem close_lift {A : Type} (oa : OracleComp (BaseSpec F G M) A)
    (st : Schnorr.AGM.State M) (cache : Cache F G M) :
    (close (liftM oa)).run (st, cache) =
      (fun p => (p.1, (st, p.2))) <$> (simulateQ impl oa).run cache := by
  have hl : ((liftM oa) : StateT (Schnorr.AGM.State M) (OracleComp (BaseSpec F G M)) A).run st =
      (fun a => (a, st)) <$> oa := by
    simp [liftM, MonadLiftT.monadLift, MonadLift.monadLift, monad_norm]
  rw [close_run, hl]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map]

theorem erase_empty : erase ({} : Reduction.State F G M) = ({}, ∅) := rfl

theorem erase_record (s : Reduction.State F G M) (key : M × G) (a : Affine F) (c : F) :
    erase (record s key a c) = ((erase s).1, (erase s).2.cacheQuery key c) := by
  apply Prod.ext
  · rfl
  · ext key'
    by_cases h : key' = key
    · subst key'; simp [erase, record]
    · simp [erase, record, h, QueryCache.cacheQuery_of_ne]

/-- Closing pure sampling leaves both the signing log and hash cache unchanged. -/
theorem close_sample (st : Schnorr.AGM.State M) (cache : Cache F G M) :
    (close (F := F) (G := G) (M := M)
      (liftM (liftComp ($ᵗ F) (BaseSpec F G M)))).run (st, cache) =
      (fun r : F => (r, (st, cache))) <$> ($ᵗ F) := by
  rw [close_lift]
  simp only [impl, OracleComp.liftComp_eq_liftM, roSim.run_liftM, Functor.map_map]

theorem close_hash (st : Schnorr.AGM.State M) (cache : Cache F G M) (key : M × G) :
    (close (F := F) (G := G) (M := M)
      (liftM ((BaseSpec F G M).query (.inr key)))).run
        (st, cache) =
      (fun p => (p.1, (st, p.2))) <$> ((M × G →ₒ F).randomOracle key).run cache := by
  have hl : (liftM ((BaseSpec F G M).query (.inr key)) :
      StateT (Schnorr.AGM.State M) (OracleComp (BaseSpec F G M)) F).run st =
      (fun a => (a, st)) <$> (liftM ((BaseSpec F G M).query (.inr key)) : OracleComp (BaseSpec F G M) F) := rfl
  rw [close_run, hl]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map, impl,
    simulateQ_spec_query, QueryImpl.add_apply]

theorem close_random (st : Schnorr.AGM.State M) (cache : Cache F G M) (n : Nat) :
    (close (F := F) (G := G) (M := M)
      (liftM ((BaseSpec F G M).query (.inl n)))).run
        (st, cache) =
      (fun v => (v, (st, cache))) <$> (unifSpec.query n : ProbComp _) := by
  have hl : (liftM ((BaseSpec F G M).query (.inl n)) :
      StateT (Schnorr.AGM.State M) (OracleComp (BaseSpec F G M)) (Fin (n + 1))).run st =
      (fun a => (a, st)) <$> (liftM ((BaseSpec F G M).query (.inl n)) : OracleComp (BaseSpec F G M) (Fin (n + 1))) := rfl
  rw [close_run, hl]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map, impl,
    simulateQ_spec_query, QueryImpl.add_apply]
  have h := unifFwdImpl.simulateQ_run (hashSpec := M × G →ₒ F)
    (unifSpec.query n : ProbComp _) cache
  simp only [simulateQ_spec_query] at h
  rw [h]
  simp only [Functor.map_map]

theorem close_modify (f : Schnorr.AGM.State M → Schnorr.AGM.State M)
    (st : Schnorr.AGM.State M) (cache : Cache F G M) :
    (close (F := F) (G := G) (M := M) (modify f)).run (st, cache) =
      pure ((), (f st, cache)) := by
  rw [close_run]
  simp [StateT.run_modify]

theorem close_reject (st : Schnorr.AGM.State M) (cache : Cache F G M) :
    (close (Schnorr.AGM.reject (F := F) (G := G))).run (st, cache) =
      pure ((), ({st with malformed := true}, cache)) := by
  exact close_modify _ st cache

end Schnorr.AGM.Reduction.Source
