import Signatures.Runtime.Caliper.SchnorrROMReplaySecondBounds

/-! The executed second pass is the original replay-aware ROM pass on the
original restart tapes. The complete first result remains paired with its output. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplaySecond
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
    [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Pass.Caller config A) (ops : Handler.Operations config) (law : Handler.SigningLaw config ops.signing)
    (fuel : Nat) (witness : Pass.Caller.Source config caller fuel)

def observed (value : Terminal.Output config × Request config) := (Pass.observed config value.1, value.2)

theorem source_original (value : {value : Request config // ready config fuel value}) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    observed config <$> source config caller ops fuel value =
      (fun result => ((some result.1, result.2), value.val)) <$>
        Schnorr.ListROM.Shared.tapeRun
          ((Schnorr.ListROM.passWith law.target
            (Subtype.val <$> witness.program
              (witness.inputView (Pass.Initialization.start config (nextInput config fuel value)).1))).run
                (value.val.2.2.val.1.1, [], []))
          (ReplayRestart.tapes (Schnorr.RawTape.restart value.val.1.1.val value.val.1.2.val
            ⟨value.val.2.2.val.2.1, value.val.2.2.val.2.2⟩)) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have original := Pass.source_tapeRun config caller ops law fuel witness
    (nextInput config fuel value) (next_ready config fuel value)
  have retained := congrArg (Functor.map (fun result => (result, value.val))) original
  simpa only [observed, source, Functor.map_map, nextInput, Pass.Replay.nextInput,
    Pass.Replay.request, ReplayRestart.source, Restart.source] using retained

theorem observe_original (tape : RandomTape w) (value : {value : Request config // ready config fuel value})
    (before : State w) (holds : (input config fuel).Holds value before) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    (fun result => (Interactive.observe (output config) result).map (observed config)) <$>
        (program config caller ops fuel).execute (Fresh.port config.handler.sampler.tape) .unit tape before =
      (fun result => some ((some result.1, result.2), value.val)) <$>
        Schnorr.ListROM.Shared.tapeRun
          ((Schnorr.ListROM.passWith law.target
            (Subtype.val <$> witness.program
              (witness.inputView (Pass.Initialization.start config (nextInput config fuel value)).1))).run
                (value.val.2.2.val.1.1, [], []))
          (ReplayRestart.tapes (Schnorr.RawTape.restart value.val.1.1.val value.val.1.2.val
            ⟨value.val.2.2.val.2.1, value.val.2.2.val.2.2⟩)) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have executed := congrArg (Functor.map (Option.map (observed config)))
    ((refines config caller ops fuel).observe tape value before holds)
  have original := congrArg (Functor.map some) (source_original config caller ops law fuel witness value)
  simp only [Functor.map_map, Option.map_some] at executed original
  exact executed.trans original

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplaySecond
