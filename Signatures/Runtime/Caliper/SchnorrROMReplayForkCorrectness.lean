import Signatures.Runtime.Caliper.SchnorrROMReplayForkOriginal

/-! The complete initialized Caliper fork observes the original raw-tape fork.
The correspondence is derived from the caller's local source witness, including
rejection, challenge sampling, restart, second selection and both outputs. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Pass.Caller config A)
    (ops : Handler.Operations config) (law : Handler.SigningLaw config ops.signing) (qH : Nat) (indexFits : qH + 1 < 2 ^ w)
    (fuel : Nat) (witness : Pass.Caller.Source config caller fuel)

theorem after_fixed (first : Terminal.Output config) (slot : Fin (qH + 1))
    (room : savedReady config fuel (counterOfIndex config qH indexFits slot, first))
    (points : (Pass.Initialization.points config).Value) (preserved : publicPoints config first = points)
    (selected : originalSelection qH (observedPass config first) = some slot) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    observed config <$> afterSource config caller ops qH fuel (counterOfIndex config qH indexFits slot, first) =
      originalAfter config qH (originalMain config caller ops law fuel witness points) (Pass.observed config first) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  rw [after_original config caller ops law qH indexFits fuel witness first slot room, preserved]
  unfold originalAfter
  change originalSelection qH (Pass.observed config first).1 = some slot at selected
  rw [selected]
  apply bind_congr
  intro replacement
  simp only [Pass.observed]
  by_cases duplicate : (Schnorr.RawTape.values (.inr ()) first.2.val.2.1)[slot.val]? = some replacement
  · simp only [duplicate, ↓reduceIte]
  · simp only [duplicate, ↓reduceIte]
    congr 1
    funext second
    unfold secondExit observedPass Pass.observed
    simp only [originalSelection, Option.bind_some]
    by_cases same : Schnorr.selectPass (G₂ := G) (K := M) PrimitiveCosts.unit qH second.1 = some slot
    · simp only [same, ↓reduceIte]
      cases (Terminal.observed config first).1 <;> rfl
    · simp only [same, ↓reduceIte]

namespace Initialized
variable (tables : fuel + 1 ≤ config.capacityPred + 1) (tapes : 4 * fuel + 3 ≤ config.sampler.capacity)

theorem source_original (value : (Pass.Initialization.points config).Value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    observed config <$> source config caller ops qH indexFits fuel tables tapes value =
      simulateQ (_root_.Schnorr.LazyROM.sample (F := F))
        (Schnorr.RawTape.fork (originalMain config caller ops law fuel witness value) qH
          (Schnorr.selectPass (G₂ := G) (K := M) PrimitiveCosts.unit qH)) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  let initial := Setup.start config fuel tables tapes value
  let main := originalMain config caller ops law fuel witness value
  have original := pass_original config caller ops law fuel witness initial.val
    (Pass.Replay.first_ready config fuel initial.val initial.property)
  calc
    observed config <$> source config caller ops qH indexFits fuel tables tapes value =
        (Pass.source config caller ops fuel initial.val >>= fun first =>
          originalAfter config qH main (Pass.observed config first)) := by
      change observed config <$> ReplayFork.source config caller ops qH indexFits fuel initial = _
      rw [source_expand, map_bind]
      apply bind_congr_of_forall_mem_support
      intro first reached
      rw [selection_original]
      cases selected : originalSelection qH (observedPass config first) with
      | none =>
          change originalSelection qH (Pass.observed config first).1 = none at selected
          simp only [map_pure, observed, originalAfter, selected]
      | some slot =>
          have room := ReplaySecond.ready_after_first config caller ops fuel initial.val initial.property
            first reached (counterOfIndex config qH indexFits slot) ⟨0, trivial⟩
          have preserved : publicPoints config first = value := Subtype.ext
            (Pass.preserves_config config caller ops fuel initial.val
              (Pass.Replay.first_ready config fuel initial.val initial.property) first reached)
          exact after_fixed config caller ops law qH indexFits fuel witness first slot room value preserved selected
    _ = ((Pass.observed config <$> Pass.source config caller ops fuel initial.val) >>=
        originalAfter config qH main) := by rw [bind_map_left]
    _ = (Schnorr.ListROM.Shared.tapeRun main ([], []) >>= fun first =>
        originalAfter config qH main (some first.1, first.2)) := by
      rw [original, bind_map_left]
      rfl
    _ = _ := original_fork_eq config qH main

include tables tapes in
theorem observe_original (tape : RandomTape w) (value : (Pass.Initialization.points config).Value)
    (before : State w) (holds : (Setup.input config).Holds value before) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    (fun result => (Interactive.observe (output config) result).map (observed config)) <$>
        (program config caller ops qH indexFits fuel).execute (Fresh.port config.handler.sampler.tape) .unit tape before =
      some <$> simulateQ (_root_.Schnorr.LazyROM.sample (F := F))
        (Schnorr.RawTape.fork (originalMain config caller ops law fuel witness value) qH
          (Schnorr.selectPass (G₂ := G) (K := M) PrimitiveCosts.unit qH)) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have executed := congrArg (Functor.map (Option.map (observed config)))
    ((refines config caller ops qH indexFits fuel tables tapes).observe tape value before holds)
  have original := congrArg (Functor.map some)
    (source_original config caller ops law qH indexFits fuel witness tables tapes value)
  simp only [Functor.map_map, Option.map_some] at executed original
  exact executed.trans original

end Initialized
end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
