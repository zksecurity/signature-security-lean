import Signatures.Runtime.Caliper.SchnorrROMReplayForkObservation

/-! The accepted replay branch observes exactly the original second pass on
the original restart tapes, followed by its original optional-index test. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

noncomputable def secondExit (qH : Nat) (first : Terminal.Output config) (slot : Fin (qH + 1))
    (second : Option (OriginalPass (M := M) (F := F) (G := G))) :=
  if originalSelection qH second = some slot then
    (observedPass config first).bind fun first => second.map fun second => (first, second)
  else none

theorem finish_observed (qH : Nat) (indexFits : qH + 1 < 2 ^ w)
    (first second : Terminal.Output config) (slot : Fin (qH + 1))
    (replacement : config.handler.sampler.tape.scalar.Value) :
    observed config (finishSource config (ReplayMatch.source config qH
      (second, ((counterOfIndex config qH indexFits slot, replacement), first)))) =
        secondExit config qH first slot (observedPass config second) := by
  have same := (PassSelection.source_original config PrimitiveCosts.unit qH second).symm.trans
    (selection_original config qH second)
  rw [second_exit_original config qH PrimitiveCosts.unit _ slot rfl, same]
  unfold secondExit
  split <;> rfl

variable (caller : Pass.Caller config A) (ops : Handler.Operations config)
    (qH : Nat) (indexFits : qH + 1 < 2 ^ w) (fuel : Nat)
    (witness : Pass.Caller.Source config caller fuel)

theorem second_original (first : Terminal.Output config) (slot : Fin (qH + 1))
    (replacement : config.handler.sampler.tape.scalar.Value)
    (room : ReplaySecond.ready config fuel ((counterOfIndex config qH indexFits slot, replacement), first)) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    observed config <$> secondSource config caller ops qH fuel
      ((counterOfIndex config qH indexFits slot, replacement), first) =
        (fun result => secondExit config qH first slot (some result.1)) <$>
          Schnorr.ListROM.Shared.tapeRun
            (originalMain config caller fuel witness (publicPoints config first))
            (ReplayRestart.tapes (Schnorr.RawTape.restart slot.val replacement.val
              ⟨first.2.val.2.1, first.2.val.2.2⟩)) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  let request : ReplaySecond.Request config := ((counterOfIndex config qH indexFits slot, replacement), first)
  let next := ReplaySecond.nextInput config fuel ⟨request, room⟩
  have original := pass_original config caller ops fuel witness next (ReplaySecond.next_ready config fuel ⟨request, room⟩)
  have viewed := congrArg (Functor.map (fun result => secondExit config qH first slot result.1)) original
  simp only [Functor.map_map] at viewed
  calc
    observed config <$> secondSource config caller ops qH fuel request =
        (fun second => secondExit config qH first slot (observedPass config second)) <$>
          Pass.source config caller ops fuel next := by
      unfold secondSource
      rw [dite_eq_left room, ReplaySecond.Selected.source, ReplaySecond.source]
      simp only [Functor.map_map]
      apply congrArg (fun view => view <$> Pass.source config caller ops fuel next)
      funext second
      exact finish_observed config qH indexFits first second slot replacement
    _ = (fun result => secondExit config qH first slot (some result.1)) <$>
        Schnorr.ListROM.Shared.tapeRun (originalMain config caller fuel witness next.2) next.1.val := viewed
    _ = _ := rfl

theorem after_original (first : Terminal.Output config) (slot : Fin (qH + 1))
    (room : savedReady config fuel (counterOfIndex config qH indexFits slot, first)) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    observed config <$> afterSource config caller ops qH fuel (counterOfIndex config qH indexFits slot, first) =
      (($ᵗ F : ProbComp F) >>= fun replacement =>
        if (Schnorr.RawTape.values (.inr ()) first.2.val.2.1)[slot.val]? = some replacement then pure none
        else (fun result => secondExit config qH first slot (some result.1)) <$>
          Schnorr.ListROM.Shared.tapeRun (originalMain config caller fuel witness (publicPoints config first))
            (ReplayRestart.tapes (Schnorr.RawTape.restart slot.val replacement
              ⟨first.2.val.2.1, first.2.val.2.2⟩))) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  let next (replacement : F) : ProbComp (Option (OriginalPass (M := M) (F := F) (G := G) × OriginalPass (M := M) (F := F) (G := G))) :=
    if (Schnorr.RawTape.values (.inr ()) first.2.val.2.1)[slot.val]? = some replacement then pure none
    else (fun result => secondExit config qH first slot (some result.1)) <$>
      Schnorr.ListROM.Shared.tapeRun (originalMain config caller fuel witness (publicPoints config first))
        (ReplayRestart.tapes (Schnorr.RawTape.restart slot.val replacement ⟨first.2.val.2.1, first.2.val.2.2⟩))
  change _ = (($ᵗ F : ProbComp F) >>= next)
  calc
    _ = (PrivateSampler.Enumerated.Direct.source config.sampler >>= fun replacement => next replacement.val) := by
      rw [afterSource_expand]
      erw [map_bind]
      apply bind_congr
      intro replacement
      by_cases duplicate : (Schnorr.RawTape.values (.inr ()) first.2.val.2.1)[slot.val]? = some replacement.val
      · simp only [counterOfIndex, duplicate, ↓reduceIte, map_pure, next]
        rfl
      · simp only [counterOfIndex, duplicate, ↓reduceIte, next]
        exact second_original config caller ops qH indexFits fuel witness first slot replacement room
    _ = _ := by
      rw [← PrivateSampler.Enumerated.Direct.uniform config.sampler]
      erw [bind_map_left]

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
