import Proofs.Runtime.Caliper.SchnorrROMReplayForkReplaySource
import Proofs.Runtime.SchnorrRawFork

/-! Original raw-tape fork equations. The optional first output only records
possible machine cutoff; the caller's source correspondence excludes it. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

noncomputable def originalAfter (qH : Nat)
    (main : OracleComp (Schnorr.RawTape.Spec F) (OriginalPass (M := M) (F := F) (G := G)))
    (first : Option (OriginalPass (M := M) (F := F) (G := G)) × Schnorr.ListROM.Shared.Tape F) :
    ProbComp (Option (OriginalPass (M := M) (F := F) (G := G) × OriginalPass (M := M) (F := F) (G := G))) :=
  letI := PrivateSampler.Enumerated.sampleable config.sampler
  match originalSelection qH first.1 with
  | none => pure none
  | some slot => ($ᵗ F : ProbComp F) >>= fun replacement =>
      if (Schnorr.RawTape.values (.inr ()) first.2.1)[slot.val]? = some replacement then pure none
      else (fun second : OriginalPass (M := M) (F := F) (G := G) × Schnorr.ListROM.Shared.Tape F =>
        if Schnorr.selectPass (G₂ := G) (K := M) PrimitiveCosts.unit qH second.1 = some slot then
          first.1.map fun first => (first, second.1) else none) <$>
        Schnorr.ListROM.Shared.tapeRun main (ReplayRestart.tapes
          (Schnorr.RawTape.restart slot.val replacement ⟨first.2.1, first.2.2⟩))

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G] in
theorem sample_lift {X : Type} (main : ProbComp X) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    simulateQ (_root_.Schnorr.LazyROM.sample (F := F)) (liftComp main (Schnorr.RawTape.Spec F)) = main := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  simp only [_root_.Schnorr.LazyROM.sample, QueryImpl.simulateQ_add_liftComp_left, simulateQ_ofLift_eq_self]

theorem original_fork_eq (qH : Nat)
    (main : OracleComp (Schnorr.RawTape.Spec F) (OriginalPass (M := M) (F := F) (G := G))) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    (Schnorr.ListROM.Shared.tapeRun main ([], []) >>= fun first =>
      originalAfter config qH main (some first.1, first.2)) =
        simulateQ (_root_.Schnorr.LazyROM.sample (F := F))
          (Schnorr.RawTape.fork main qH (Schnorr.selectPass (G₂ := G) (K := M) PrimitiveCosts.unit qH)) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  unfold Schnorr.ListROM.Shared.tapeRun
  simp only [bind_map_left, Schnorr.RawTape.fork, simulateQ_bind]
  apply bind_congr
  intro first
  unfold originalAfter originalSelection
  simp only [Option.bind_some]
  cases selected : Schnorr.selectPass (G₂ := G) (K := M) PrimitiveCosts.unit qH first.1 with
  | none => simp only [simulateQ_pure]
  | some slot =>
      simp only [simulateQ_bind, sample_lift]
      apply bind_congr
      intro replacement
      by_cases duplicate : (Schnorr.RawTape.values (.inr ()) first.2.saved)[slot.val]? = some replacement
      · simp only [duplicate, ↓reduceIte, simulateQ_pure]
      · simp only [duplicate, ↓reduceIte, Schnorr.ListROM.Shared.tapeRun,
          StateT.run', simulateQ_bind, bind_map_left, Functor.map_map, Option.map_some]
        rw [map_eq_bind_pure_comp]
        apply bind_congr
        intro second
        by_cases same : Schnorr.selectPass (G₂ := G) (K := M) PrimitiveCosts.unit qH second.1 = some slot
        all_goals simp only [Function.comp_apply, same, ↓reduceIte, simulateQ_pure]

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
