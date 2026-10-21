import Signatures.Runtime.Caliper.SchnorrROMReplaySecondRoutingBounds

/-! A constructed restart and second execution, retaining the complete first
result in an actual saved buffer. Its admission is derived from the first pass;
no second-pass invariant or completed implementation is supplied by the caller. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplaySecond
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Pass.Caller config A) (ops : Handler.Operations config)

def retainedPass (fuel : Nat) : Interactive.Code w :=
  Interactive.retain (Pass.program config caller ops fuel)
    (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape) (Pass.program config caller ops fuel))
    (Pass.Initialization.input config).encoding.words (first config).encoding.words (rawInput config).encoding.words
def program (fuel : Nat) : Interactive.Code w :=
  .seq (.compute (initializeReplay config fuel).code) (retainedPass config caller ops fuel)
def source (fuel : Nat) (value : {value : Request config // ready config fuel value}) : ProbComp (Terminal.Output config × Request config) :=
  (fun second => (second, value.val)) <$> Pass.source config caller ops fuel (nextInput config fuel value)

theorem pass_refines (fuel : Nat) : Interactive.RefinesOn (Pass.Initialization.admitted config fuel)
    (Fresh.port config.handler.sampler.tape) .unit (Pass.Initialization.input config) (first config)
    (Pass.source config caller ops fuel) (Pass.program config caller ops fuel) := by
  simpa only [id_map] using (Pass.refines config caller ops fuel).viewOutput (first config) id
    (PassSelection.pass_bytes config (caller.pending config) (caller.terminalRoom config))

theorem refines (fuel : Nat) : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit
    (input config fuel) (output config) (source config caller ops fuel) (program config caller ops fuel) := by
  have retained := (pass_refines config caller ops fuel).retain (by decide) (rawInput config)
    config.sampler.wordFits (secondInput config).fits (output config).fits
  have prepared := (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (initializeReplay config fuel)).on (fun _ => True)
  have joined := prepared.seq retained (by
    intro value _ answer reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst answer
    exact next_ready config fuel value)
  intro tape value before holds
  simpa only [source, program, retainedPass, output, pure_bind] using joined tape value trivial before holds

theorem retained_first (fuel : Nat) (value : {value : Request config // ready config fuel value})
    (answer) (reached : answer ∈ support (source config caller ops fuel value)) : answer.2 = value.val := by
  simp only [source, support_map, Set.mem_image] at reached
  obtain ⟨_, _, rfl⟩ := reached
  rfl
theorem ready_after_first (fuel : Nat) (value : Pass.Initialization.Input config)
    (room : Pass.Replay.ready config fuel value) (first : Terminal.Output config)
    (reached : first ∈ support (Pass.source config caller ops fuel value))
    (slot : config.handler.sampler.tape.counter.Value) (replacement : config.handler.sampler.tape.scalar.Value) :
    ready config fuel ((slot, replacement), first) := by
  have growth := Pass.tape_lengths config ops caller fuel value (Pass.Replay.first_ready config fuel value room) first reached
  exact ⟨room.1, by have := room.2; change first.2.val.2.1.length + (2 * fuel + 2) ≤ _; omega⟩

theorem buffers (fuel : Nat) : ((program config caller ops fuel).lower (Fresh.port config.handler.sampler.tape)).memBound ≤
    Pass.bufferBudget config caller ops + 1 := by
  have prepared := initialization_buffers config fuel
  have retained := Interactive.retain_buffers (Fresh.port config.handler.sampler.tape) (Pass.program config caller ops fuel)
    (Pass.Initialization.input config).encoding.words (first config).encoding.words (rawInput config).encoding.words
  have body := Pass.buffers config caller ops fuel
  change ((retainedPass config caller ops fuel).lower _).memBound ≤ _ at retained
  change max (initializeReplay config fuel).code.memBound ((retainedPass config caller ops fuel).lower _).memBound ≤ _
  unfold Pass.bufferBudget at *
  omega
theorem descriptionFits (room : Pass.replayNameRoom config caller ops) (fuel : Nat) :
    ((program config caller ops fuel).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  .seq config.sampler.wordFits (.compute (initializeReplay config fuel).description_fits)
    (Interactive.retain_descriptionFits _ _ _ _ _ _ config.sampler.wordFits
      (Pass.descriptionFits config caller ops fuel) (Pass.savedNameFits config caller ops room fuel)
      (Pass.Initialization.input config).fits (rawInput config).fits (output config).fits)

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplaySecond
