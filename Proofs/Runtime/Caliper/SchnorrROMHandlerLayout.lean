import Proofs.Runtime.Caliper.SchnorrROMHashBounds
import Proofs.Runtime.Caliper.SchnorrROMRandomBounds
import Proofs.Runtime.Caliper.TagBounds

/-! The ROM service uses the original request order: private randomness, hash,
then signing. Each branch carries the same shared store. Reply tags and padding
are produced by executed copies; no request or state is retained implicitly. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G : Type} [Zero F] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

abbrev Input := ((Random.input config).Value ⊕ (Hash.input config).Value) ⊕ config.handler.input.Value
abbrev Output := ((Random.output config).Value ⊕ (Hash.output config).Value) ⊕ config.handler.output.Value

theorem input_widths :
    (Random.input config).representation.encoding.words ≤ 4 * config.handler.width ∧
    (Hash.input config).representation.encoding.words ≤ 4 * config.handler.width ∧
    config.handler.input.representation.encoding.words ≤ 4 * config.handler.width := by
  have saved := FinalHash.store_le config
  have key := FinalHash.key_le config
  have positive := Random.positive config
  change 1 + _ ≤ _ ∧ config.handler.core.key.representation.encoding.words + _ ≤ _ ∧
    config.message.representation.encoding.words + _ ≤ _
  change config.message.representation.encoding.words + config.point.representation.encoding.words ≤ _ at key
  change 1 + _ ≤ _ ∧ (config.message.representation.encoding.words + config.point.representation.encoding.words) + _ ≤ _ ∧ _
  omega

omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem output_widths :
    (Random.output config).representation.encoding.words ≤ 5 * config.handler.width ∧
    (Hash.output config).representation.encoding.words ≤ 5 * config.handler.width ∧
    config.handler.output.representation.encoding.words ≤ 5 * config.handler.width := by
  have saved := FinalHash.store_le config
  have key := FinalHash.key_le config
  have positive := Random.positive config
  change config.message.representation.encoding.words + config.point.representation.encoding.words ≤ _ at key
  change (1 + 1) + _ ≤ _ ∧ 1 + _ ≤ _ ∧ (config.point.representation.encoding.words + 1) + _ ≤ _
  omega

def innerInput := (Random.input config).representation.sum (Hash.input config).representation
  (width_pos config.sampler.wordFits) (config.handler.fits_of_le (by
    have := input_widths config; have := Random.positive config; omega))
def input : Representation w (Input config) := (innerInput config).sum config.handler.input.representation
  (width_pos config.sampler.wordFits) (config.handler.fits_of_le (by
    have := input_widths config; have := Random.positive config
    change 1 + max (1 + max _ _) _ ≤ _; omega))
def innerOutput := (Random.output config).representation.sum (Hash.output config).representation
  (width_pos config.sampler.wordFits) (config.handler.fits_of_le (by
    have := output_widths config; have := Random.positive config; omega))
def output : Representation w (Output config) := (innerOutput config).sum config.handler.output.representation
  (width_pos config.sampler.wordFits) (config.handler.fits_of_le (by
    have := output_widths config; have := Random.positive config
    change 1 + max (1 + max _ _) _ ≤ _; omega))

theorem packet_widths : (innerInput config).encoding.words ≤ 5 * config.handler.width ∧
    (input config).encoding.words ≤ 6 * config.handler.width ∧
    (innerOutput config).encoding.words ≤ 6 * config.handler.width ∧
    (output config).encoding.words ≤ 7 * config.handler.width := by
  have := input_widths config; have := output_widths config; have := Random.positive config
  change 1 + max _ _ ≤ _ ∧ 1 + max (1 + max _ _) _ ≤ _ ∧
    1 + max _ _ ≤ _ ∧ 1 + max (1 + max _ _) _ ≤ _
  omega

def randomTag : Realizer .unit (Random.output config).representation (output config) (fun value => .inl (.inl value)) :=
  (inlRealizer .unit (by decide) (Random.output config).representation (Hash.output config).representation
    config.sampler.wordFits (innerOutput config).fits).then
      (inlRealizer .unit (by decide) (innerOutput config) config.handler.output.representation
        config.sampler.wordFits (output config).fits)
def hashTag : Realizer .unit (Hash.output config).representation (output config) (fun value => .inl (.inr value)) :=
  (inrRealizer .unit (by decide) (Random.output config).representation (Hash.output config).representation
    config.sampler.wordFits (innerOutput config).fits).then
      (inlRealizer .unit (by decide) (innerOutput config) config.handler.output.representation
        config.sampler.wordFits (output config).fits)
def signingTag : Realizer .unit config.handler.output.representation (output config) Sum.inr :=
  inrRealizer .unit (by decide) (innerOutput config) config.handler.output.representation
    config.sampler.wordFits (output config).fits

/-- Three reserved tape cells: enough for the full-field pair of draws and for
the nonzero-nonce triple. -/
def signingReady (value : config.handler.input.Value) : Prop :=
  PrivateHandler.Reserved config.handler.sampler.tape 3 (Signing.Handler.tapes config.handler value)
theorem signingReady_pair (value : config.handler.input.Value) (valid : signingReady config value) :
    Signing.Handler.ready config.handler 1 value := by
  unfold signingReady PrivateHandler.Reserved at valid
  change (Signing.Handler.tapes config.handler value).val.1.length + (1 + 1) ≤ config.handler.sampler.tape.capacity
  omega
def ready : Input config → Prop :=
  Sum.elim (Sum.elim (fun _ => True) (Hash.ready config)) (signingReady config)

end Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
