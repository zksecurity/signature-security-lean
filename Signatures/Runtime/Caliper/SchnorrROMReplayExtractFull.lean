import Signatures.Runtime.Caliper.SchnorrROMReplayExtractSource
import Signatures.Runtime.Caliper.SchnorrROMReplayForkCorrectness
import Signatures.Runtime.Caliper.SchnorrROMReplayInitializedBounds
import Signatures.Runtime.SchnorrReduction

/-! The complete executed DLog solver of the ROM reduction: the verified
initialized fork controller followed by the executed extractor. Its source is
derived from the controller correspondence and the extractor correspondence; the
final law is the original `RawTape.fork … >>= liftRandom ∘ extractFork`. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} (config : Signing.Enumerated.Configuration w M F G)

section Program
variable [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G] [DecidableEq F] [Sub F] [Div F]
    (caller : Pass.Caller config A) (ops : Handler.Operations config) (qH : Nat) (indexFits : qH + 1 < 2 ^ w)
    (arith : Arithmetic config)

/-- The full program: the initialized fork controller, then the extractor. -/
def fullProgram (fuel : Nat) : Interactive.Code w :=
  .seq (Initialized.program config caller ops qH indexFits fuel) (code config arith)
def fullSource (fuel : Nat) (tables : fuel + 1 ≤ config.capacityPred + 1)
    (tapes : 4 * fuel + 3 ≤ config.sampler.capacity) (value : (Pass.Initialization.points config).Value) :
    ProbComp config.handler.sampler.tape.scalar.Value :=
  Initialized.source config caller ops qH indexFits fuel tables tapes value >>= source config

theorem full_refines (fuel : Nat) (tables : fuel + 1 ≤ config.capacityPred + 1)
    (tapes : 4 * fuel + 3 ≤ config.sampler.capacity) :
    Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit (Setup.input config)
      config.handler.sampler.tape.scalar.representation
      (fullSource config caller ops qH indexFits fuel tables tapes) (fullProgram config caller ops qH indexFits arith fuel) :=
  (Initialized.refines config caller ops qH indexFits fuel tables tapes).seq (refines config arith)

end Program

section Original
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G]
    (caller : Pass.Caller config A) (ops : Handler.Operations config) (qH : Nat) (indexFits : qH + 1 < 2 ^ w)
    (fuel : Nat) (witness : Pass.Caller.Source config caller fuel)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G] in
theorem sample_liftRandom {X : Type} (main : ProbComp X) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    simulateQ (_root_.Schnorr.LazyROM.sample (F := F)) (Schnorr.liftRandom (F := F) main) = main := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  rw [Schnorr.liftRandom_eq_liftComp]
  exact sample_lift config main

/-- The whole executed solver has exactly the law of the ROM theorem's DLog
reduction `ListROM.dlogReduction` on the caller's original program. -/
theorem fullSource_original (tables : fuel + 1 ≤ config.capacityPred + 1)
    (tapes : 4 * fuel + 3 ≤ config.sampler.capacity) (value : (Pass.Initialization.points config).Value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    Subtype.val <$> fullSource config caller ops qH indexFits fuel tables tapes value =
      simulateQ (_root_.Schnorr.LazyROM.sample (F := F))
        (Schnorr.RawTape.fork (originalMain config caller fuel witness value) qH
          (Schnorr.selectPass (G₂ := G) (K := M) PrimitiveCosts.unit qH) >>= fun result =>
            Schnorr.liftRandom (Schnorr.extractFork (G₂ := G) (K := M) result)) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have controller := Initialized.source_original config caller ops qH indexFits fuel witness tables tapes value
  calc
    Subtype.val <$> fullSource config caller ops qH indexFits fuel tables tapes value =
        (Initialized.source config caller ops qH indexFits fuel tables tapes value >>= fun result =>
          Schnorr.extractFork (G₂ := G) (K := M) (observed config result)) := by
      unfold fullSource
      rw [map_bind]
      exact bind_congr (fun result => source_original config result)
    _ = (observed config <$> Initialized.source config caller ops qH indexFits fuel tables tapes value) >>=
        Schnorr.extractFork (G₂ := G) (K := M) := by rw [bind_map_left]
    _ = _ := by
      rw [controller, simulateQ_bind]
      exact bind_congr (fun result => (sample_liftRandom config _).symm)

include witness in
/-- The executed solver, observed on the scalar output, is the original
reduction law; every terminating run decodes. -/
theorem full_observe_original (tables : fuel + 1 ≤ config.capacityPred + 1)
    (tapes : 4 * fuel + 3 ≤ config.sampler.capacity) (arith : Arithmetic config)
    (tape : RandomTape w) (value : (Pass.Initialization.points config).Value)
    (before : State w) (holds : (Setup.input config).Holds value before) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    (fun result => (Interactive.observe config.handler.sampler.tape.scalar.representation result).map Subtype.val) <$>
        (fullProgram config caller ops qH indexFits arith fuel).execute (Fresh.port config.handler.sampler.tape) .unit tape before =
      some <$> simulateQ (_root_.Schnorr.LazyROM.sample (F := F))
        (Schnorr.RawTape.fork (originalMain config caller fuel witness value) qH
          (Schnorr.selectPass (G₂ := G) (K := M) PrimitiveCosts.unit qH) >>= fun result =>
            Schnorr.liftRandom (Schnorr.extractFork (G₂ := G) (K := M) result)) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have executed := congrArg (Functor.map (Option.map Subtype.val))
    ((full_refines config caller ops qH indexFits arith fuel tables tapes).observe tape value before holds)
  have original := congrArg (Functor.map some)
    (fullSource_original config caller ops qH indexFits fuel witness tables tapes value)
  simp only [Functor.map_map, Option.map_some] at executed original
  exact executed.trans original

end Original
end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
