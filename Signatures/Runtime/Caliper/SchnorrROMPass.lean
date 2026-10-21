import Signatures.Runtime.Caliper.SchnorrROMPassInitialization
import Signatures.Runtime.Caliper.SchnorrROMPassCallerSource

/-! A complete initialized ROM pass. Setup, adaptive oracle calls and the final
LIVE hash execute as one program; every supported exit retains its private store. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Pass
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
section Runtime
variable {w : Nat} {M F G A : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Caller config A) (ops : Handler.Operations config)

def program (fuel : Nat) : Interactive.Code w :=
  .seq (.compute (Initialization.code config).code) (finishCode config caller ops fuel)
def source (fuel : Nat) (value : Initialization.Input config) : ProbComp (Terminal.Output config) :=
  finishSource config caller ops fuel (Initialization.start config value)

theorem refines (fuel : Nat) : Interactive.RefinesOn (Initialization.admitted config fuel) (Fresh.port config.handler.sampler.tape) .unit
    (Initialization.input config) (output config caller) (source config caller ops fuel) (program config caller ops fuel) := by
  have refined := ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (Initialization.code config)).on
    (Initialization.admitted config fuel)).seq (finish_refines config caller ops fuel) (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact Initialization.reserved config fuel value valid)
  unfold source program
  simpa only [pure_bind] using refined

theorem preserves_config (fuel : Nat) (value : Initialization.Input config) (room : Initialization.admitted config fuel value)
    (answer) (reached : answer ∈ support (source config caller ops fuel value)) : answer.2.val.1.1 = value.2.val :=
  finish_preserves_config config caller ops fuel (Initialization.start config value) (Initialization.reserved config fuel value room) answer reached
end Runtime

section Original
variable {w : Nat} {M F G A : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
    [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Caller config A) (ops : Handler.Operations config) (law : Handler.SigningLaw config ops.signing)
    (fuel : Nat) (witness : Caller.Source config caller fuel)

theorem source_original (value : Initialization.Input config) (room : Initialization.admitted config fuel value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    Terminal.observed config <$> source config caller ops fuel value =
      (fun result => (some result.1, result.2)) <$>
        (Schnorr.ListROM.Shared.interpret (Schnorr.ListROM.passWith law.target
          (Subtype.val <$> witness.program (witness.inputView (Initialization.start config value).1)))).run
            ((value.2.val, [], []), value.1.val) :=
  finish_source_original config caller ops law fuel witness
    (Initialization.start config value) (Initialization.reserved config fuel value room)

def observed (value : Terminal.Output config) :
    Option (((M × G × F) × F) × Schnorr.ListROM.Shared.Caches F G M) × Schnorr.ListROM.Shared.Tape F :=
  ((Terminal.observed config value).1.map (fun result => (result, value.2.val.1)), value.2.val.2)

theorem source_tapeRun (value : Initialization.Input config) (room : Initialization.admitted config fuel value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    observed config <$> source config caller ops fuel value =
      (fun result => (some result.1, result.2)) <$>
        Schnorr.ListROM.Shared.tapeRun
          ((Schnorr.ListROM.passWith law.target
            (Subtype.val <$> witness.program (witness.inputView (Initialization.start config value).1))).run
              (value.2.val, [], [])) value.1.val := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have original := source_original config caller ops law fuel witness value room
  have mapped := congrArg (Functor.map (fun result : Option ((M × G × F) × F) × Schnorr.ListROM.Shared.Store F G M =>
    (result.1.map (fun forge => (forge, result.2.1)), result.2.2))) original
  unfold observed
  simpa only [Schnorr.ListROM.Shared.interpret, StateT.run, Functor.map_map, Option.map_some, Terminal.observed] using mapped

theorem observe_original (tape : RandomTape w) (value : Initialization.Input config) (room : Initialization.admitted config fuel value)
    (before : State w) (holds : (Initialization.input config).Holds value before) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    (fun result => (Interactive.observe (output config caller) result).map (observed config)) <$>
        (program config caller ops fuel).execute (Fresh.port config.handler.sampler.tape) .unit tape before =
      (fun result => some (some result.1, result.2)) <$>
        Schnorr.ListROM.Shared.tapeRun
          ((Schnorr.ListROM.passWith law.target
            (Subtype.val <$> witness.program (witness.inputView (Initialization.start config value).1))).run
              (value.2.val, [], [])) value.1.val := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have executed := congrArg (Functor.map (Option.map (observed config)))
    ((refines config caller ops fuel).observe tape value room before holds)
  have original := congrArg (Functor.map some) (source_tapeRun config caller ops law fuel witness value room)
  simp only [Functor.map_map, Option.map_some] at executed original
  exact executed.trans original
end Original
end Signatures.Runtime.CaliperBackend.SchnorrROM.Pass
