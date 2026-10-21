import Signatures.Runtime.Caliper.SchnorrROMReplaySecondRouting

/-! Resource bounds for preparing the second pass. Every duplicate of the
first result and every copy of the reset tapes is included. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplaySecond
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

def resetTime := ReplayRestart.timeBudget config.handler.sampler.tape +
  8 * (ReplayRestart.input config.handler.sampler.tape).representation.encoding.words +
  8 * (Pass.Initialization.tapes config).representation.encoding.words + 12 * (rawInput config).encoding.words
def resetWords := ReplayRestart.codeBudget config.handler.sampler.tape +
  26 * (ReplayRestart.input config.handler.sampler.tape).representation.encoding.words +
  26 * (Pass.Initialization.tapes config).representation.encoding.words + 39 * (rawInput config).encoding.words + 39
theorem reset_time (value) : (reset config).time value ≤ resetTime config := by
  have retained := (ReplayRestart.implementation config.handler.sampler.tape).program.retain_time_unit_le
    (rawInput config) config.sampler.wordFits (resetNameFits config) (prepared config).fits (restarted config).fits value
  have body := (ReplayRestart.bounded config.handler.sampler.tape).time_le value.1
  change _ ≤ _ + 8 * _ + 8 * (Pass.Initialization.tapes config).representation.encoding.words + 12 * _ at retained
  unfold resetTime
  exact retained.trans (by omega)
theorem reset_words : descriptionWords (reset config).code ≤ resetWords config := by
  have retained := (ReplayRestart.implementation config.handler.sampler.tape).program.retain_descriptionWords_le
    (by decide) (rawInput config) config.sampler.wordFits (resetNameFits config) (prepared config).fits (restarted config).fits
  have body := (ReplayRestart.bounded config.handler.sampler.tape).code_le
  change _ ≤ _ + 26 * _ + 26 * (Pass.Initialization.tapes config).representation.encoding.words + 39 * _ + 39 at retained
  unfold resetWords
  exact retained.trans (by omega)
theorem reset_buffers : (reset config).code.memBound ≤ 7 := by
  have retained := (ReplayRestart.implementation config.handler.sampler.tape).program.retain_buffers
    (by decide) (rawInput config) config.sampler.wordFits (resetNameFits config) (prepared config).fits (restarted config).fits
  have body := ReplayRestart.buffers config.handler.sampler.tape
  exact retained.trans (by omega)
theorem reset_names (slots : Nat) : NamesAccounted (reset config).code slots :=
  Retain.names (ReplayRestart.names config.handler.sampler.tape slots)
    (ReplayRestart.input config.handler.sampler.tape).representation.encoding.words
    (Pass.Initialization.tapes config).representation.encoding.words (rawInput config).encoding.words

def initializationTime := 8 * (prepared config).encoding.words + resetTime config + 8 * (secondInput config).encoding.words
def initializationWords := 26 * (prepared config).encoding.words + resetWords config + 26 * (secondInput config).encoding.words + 30
theorem initialization_time (fuel : Nat) (value) : (initializeReplay config fuel).time value ≤ initializationTime config := by
  have prepared : (prepare config fuel).time value ≤ 8 * (prepared config).encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ _
  have reset := reset_time config (prepareValue config fuel value)
  have repacked : (repack config).time (resetValue config (prepareValue config fuel value)) ≤
      8 * (secondInput config).encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ _
  change (prepare config fuel).time value + (ReplaySecond.reset config).time (prepareValue config fuel value) +
    (repack config).time (resetValue config (prepareValue config fuel value)) ≤ _
  unfold initializationTime
  omega
theorem initialization_words (fuel : Nat) : descriptionWords (initializeReplay config fuel).code ≤ initializationWords config := by
  have prepared : descriptionWords (prepare config fuel).code ≤ 26 * (prepared config).encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
  have reset := reset_words config
  have repacked : descriptionWords (repack config).code ≤ 26 * (secondInput config).encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
  change descriptionWords (((prepare config fuel).code ;; (ReplaySecond.reset config).code) ;; (repack config).code) ≤ _
  rw [descriptionWords_seq, descriptionWords_seq]
  unfold initializationWords
  omega
theorem initialization_buffers (fuel : Nat) : (initializeReplay config fuel).code.memBound ≤ 7 := by
  have prepared : (prepare config fuel).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
  have reset := reset_buffers config
  have repacked : (repack config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
  change max (max (prepare config fuel).code.memBound (ReplaySecond.reset config).code.memBound) (repack config).code.memBound ≤ _
  omega
theorem initialization_names (fuel slots : Nat) : NamesAccounted (initializeReplay config fuel).code slots :=
  ((ByteRoute.names _ _ _ _ _ _ _ _ slots).seq (reset_names config slots)).seq (ByteRoute.names _ _ _ _ _ _ _ _ slots)

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplaySecond
