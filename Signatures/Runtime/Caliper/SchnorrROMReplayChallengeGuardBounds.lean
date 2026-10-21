import Signatures.Runtime.Caliper.SchnorrROMReplayChallengeGuard

/-! The saved-tape guard account includes routing its arguments and retaining
all bytes of the replay request throughout the public-cell scan. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayChallenge.Guard
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G : Type} [DecidableEq F] (config : Signing.Enumerated.Configuration w M F G)

def timeBudget := FreshGuard.polynomialTime config.handler.sampler.tape + 8 * (prepared config).encoding.words +
  8 * (argument config).encoding.words + 8 * config.handler.sampler.tape.boolean.representation.encoding.words +
    12 * (ReplaySecond.rawInput config).encoding.words
def codeBudget := FreshGuard.polynomialWords config.handler.sampler.tape + 26 * (prepared config).encoding.words +
  26 * (argument config).encoding.words + 26 * config.handler.sampler.tape.boolean.representation.encoding.words +
    39 * (ReplaySecond.rawInput config).encoding.words + 54

theorem time (value : ReplaySecond.Request config) : (realizer config).time value ≤ timeBudget config := by
  have prepared : (prepare config).time value ≤ 8 * (ReplayChallenge.Guard.prepared config).encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ _
  have kept := (FreshGuard.implementation config.handler.sampler.tape).program.retain_time_unit_le (ReplaySecond.rawInput config)
    config.sampler.wordFits (savedNameFits config) (ReplayChallenge.Guard.prepared config).fits (output config).fits (guardValue config value, value)
  simp only at kept
  have tested := (FreshGuard.polynomial_bounded config.handler.sampler.tape).time_le (guardValue config value)
  change (retained config).time (guardValue config value, value) ≤
    (FreshGuard.implementation config.handler.sampler.tape).program.time (guardValue config value) +
      8 * (argument config).encoding.words + 8 * config.handler.sampler.tape.boolean.representation.encoding.words +
        12 * (ReplaySecond.rawInput config).encoding.words at kept
  change (prepare config).time value + (retained config).time (guardValue config value, value) ≤ _
  unfold timeBudget
  omega

theorem words : descriptionWords (realizer config).code ≤ codeBudget config := by
  have prepared : descriptionWords (prepare config).code ≤ 26 * (ReplayChallenge.Guard.prepared config).encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
  have kept := (FreshGuard.implementation config.handler.sampler.tape).program.retain_descriptionWords_le (by decide) (ReplaySecond.rawInput config)
    config.sampler.wordFits (savedNameFits config) (ReplayChallenge.Guard.prepared config).fits (output config).fits
  have tested := (FreshGuard.polynomial_bounded config.handler.sampler.tape).code_le
  change descriptionWords (retained config).code ≤ descriptionWords (FreshGuard.implementation config.handler.sampler.tape).program.code +
    26 * (argument config).encoding.words + 26 * config.handler.sampler.tape.boolean.representation.encoding.words +
      39 * (ReplaySecond.rawInput config).encoding.words + 39 at kept
  change descriptionWords ((prepare config).code ;; (retained config).code) ≤ _
  rw [descriptionWords_seq]
  unfold codeBudget
  omega

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayChallenge.Guard
