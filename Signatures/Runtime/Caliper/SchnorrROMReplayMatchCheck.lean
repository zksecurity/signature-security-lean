import Signatures.Runtime.Caliper.SchnorrROMReplayMatchLayout

/-! The selected index is compared with the saved target by executed word
equality. A rejected selector stays rejected even when both indices are zero. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayMatch.Check
open Caliper BoundedSource
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

def selected := Constructed.first (Selection.result config) config.handler.sampler.tape.counter
  config.sampler.wordFits (argument config).representation.fits
def flag := (selected config).then (Constructed.first (Selection.boolean config) (Selection.Guard.index config)
  config.sampler.wordFits (Selection.result config).representation.fits)
def ordinal := (selected config).then (Constructed.second (Selection.boolean config) (Selection.Guard.index config)
  config.sampler.wordFits (Selection.result config).representation.fits)
def target := Constructed.second (Selection.result config) config.handler.sampler.tape.counter
  config.sampler.wordFits (argument config).representation.fits
def indices : Constructed (argument config)
    (Natural.pair (config.capacityPred + 2) (2 ^ w) config.sampler.wordFits (Nat.succ_le_iff.mpr config.countFits) le_rfl)
    (fun value => (value.1.2, value.2)) :=
  (ordinal config).pair (target config) config.sampler.wordFits
    (by change max 2 2 < _; have := config.sampler.wordFits; omega)
    (by change 2 < _; have := config.sampler.wordFits; omega)
    (by change 3 + 3 < _; have := config.sampler.wordFits; omega)
    (by change 1 + 3 < _; have := config.sampler.wordFits; omega)
    (by change 1 + 1 < _; have := config.sampler.wordFits; omega)
def equal := (indices config).then (Constructed.equal (config.capacityPred + 2) (2 ^ w)
  config.sampler.wordFits (Nat.succ_le_iff.mpr config.countFits) le_rfl)
def rejected := Constructed.constant (argument config) (Selection.boolean config) ⟨false, trivial⟩ config.sampler.wordFits
def source (value : (Bool × Nat) × Nat) : Bool := value.1.1 && decide (value.1.2 = value.2)
def constructed : Constructed (argument config) (Selection.boolean config) source :=
  (Constructed.branch config.sampler.wordFits (flag config) (equal config) (rejected config)
    (by change max 2 2 < _; have := config.sampler.wordFits; omega)
    (by change 3 + 3 < _; have := config.sampler.wordFits; omega)
    (by change 1 + 3 < _; have := config.sampler.wordFits; omega)).castFunction (by
      funext value
      rcases value with ⟨⟨flag, ordinal⟩, target⟩
      cases flag <;> rfl)
theorem buffers : (constructed config).buffers = 3 := rfl
theorem nameFits : (constructed config).implementation.program.savedBuffer < 2 ^ w :=
  (constructed config).nameFits config.sampler.wordFits (by rw [buffers]; have := config.sampler.wordFits; omega)
def retained := (constructed config).implementation.program.retain (by decide) (frame config)
  config.sampler.wordFits (nameFits config) (checking config).fits (output config).fits

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayMatch.Check
