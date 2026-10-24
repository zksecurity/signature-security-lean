import Proofs.Runtime.Caliper.SchnorrROMHandlerInvariant
import Proofs.Runtime.Caliper.SumContextMerge

/-! Independent caller requests/replies and private ROM state. Distribution
and reconstruction move the store past union padding by executed word copies.
The random reply carries its range; other replies use the pending query's type. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.CallerPackets
open Caliper BoundedSource
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

abbrev randomRequest := (SchnorrROMTape.Reply.range config.handler.sampler.tape).representation
abbrev hashRequest := config.handler.core.key.representation
abbrev signingRequest := config.message.representation
abbrev randomReply := (Random.reply config).representation
abbrev hashReply := config.handler.sampler.tape.scalar.representation
abbrev signingReply := config.handler.core.reply.representation
abbrev stored := config.handler.store.representation

def width := 4 + (randomRequest config).encoding.words + (hashRequest config).encoding.words +
  (signingRequest config).encoding.words + (randomReply config).encoding.words + (hashReply config).encoding.words +
  (signingReply config).encoding.words + (stored config).encoding.words
theorem width_fits : width config < 2 ^ w := by
  have key := FinalHash.key_le config
  have saved := FinalHash.store_le config
  have positive := Random.positive config
  apply config.handler.fits_of_le
  unfold width
  change config.message.representation.encoding.words + config.point.representation.encoding.words ≤ _ at key
  change 4 + 1 + (config.message.representation.encoding.words + config.point.representation.encoding.words) +
    config.message.representation.encoding.words + (1 + 1) + 1 + (config.point.representation.encoding.words + 1) +
    config.handler.store.representation.encoding.words ≤ _
  omega
theorem fits {words : Nat} (bound : words ≤ width config) : words < 2 ^ w := bound.trans_lt (width_fits config)

abbrev Request := ((SchnorrROMTape.Reply.range config.handler.sampler.tape).Value ⊕ config.handler.core.key.Value) ⊕ config.message.Value
abbrev Packet := Request config × config.handler.store.Value
abbrev Raw := (((SchnorrROMTape.Reply.range config.handler.sampler.tape).Value × config.handler.store.Value) ⊕
  (config.handler.core.key.Value × config.handler.store.Value)) ⊕ (config.message.Value × config.handler.store.Value)

def innerRequest := (randomRequest config).sum (hashRequest config) (width_pos config.sampler.wordFits)
  (fits config (by unfold width; omega))
def request : Representation w (Request config) := (innerRequest config).sum (signingRequest config) (width_pos config.sampler.wordFits)
  (fits config (by change 1 + max (1 + max _ _) _ ≤ _; unfold width; omega))
def input : Representation w (Packet config) := (request config).prod (stored config)
  (fits config (by change 1 + max (1 + max _ _) _ + _ ≤ _; unfold width; omega))
def randomRaw := (randomRequest config).prod (stored config) (fits config (by unfold width; omega))
def hashRaw := (hashRequest config).prod (stored config) (fits config (by unfold width; omega))
def signingRaw := (signingRequest config).prod (stored config) (fits config (by unfold width; omega))
def innerInput := (innerRequest config).prod (stored config)
  (fits config (by change 1 + max _ _ + _ ≤ _; unfold width; omega))
def innerRaw := (randomRaw config).sum (hashRaw config) (width_pos config.sampler.wordFits)
  (fits config (by change 1 + max (_ + _) (_ + _) ≤ _; unfold width; omega))
def raw : Representation w (Raw config) := (innerRaw config).sum (signingRaw config) (width_pos config.sampler.wordFits)
  (fits config (by change 1 + max (1 + max (_ + _) (_ + _)) (_ + _) ≤ _; unfold width; omega))

def prepared (value : Packet config) : Raw config :=
  match value.1 with
  | .inl (.inl range) => .inl (.inl (range, value.2))
  | .inl (.inr key) => .inl (.inr (key, value.2))
  | .inr message => .inr (message, value.2)
def prepare : Realizer .unit (input config) (raw config) (prepared config) :=
  ((SumContext.distribute (innerRequest config) (signingRequest config) (stored config)
    config.sampler.wordFits (input config).fits).then
      (branchRealizer .unit (by decide) (innerInput config) (signingRaw config) (raw config)
        ((SumContext.distribute (randomRequest config) (hashRequest config) (stored config)
          config.sampler.wordFits (innerInput config).fits).then
            (inlRealizer .unit (by decide) (innerRaw config) (signingRaw config) config.sampler.wordFits (raw config).fits))
        (inrRealizer .unit (by decide) (innerRaw config) (signingRaw config) config.sampler.wordFits (raw config).fits)
        config.sampler.wordFits (fits config (by
          change 1 + max ((1 + max _ _) + _) (_ + _) ≤ _; unfold width; omega)))).viewOutput
            (raw config) (prepared config) (by intro value; rcases value with ⟨(range | key) | message, saved⟩ <;> rfl)

abbrev Reply := ((Random.reply config).Value ⊕ config.handler.sampler.tape.scalar.Value) ⊕ config.handler.core.reply.Value
def innerReply := (randomReply config).sum (hashReply config) (width_pos config.sampler.wordFits)
  (fits config (by unfold width; omega))
def reply : Representation w (Reply config) := (innerReply config).sum (signingReply config) (width_pos config.sampler.wordFits)
  (fits config (by change 1 + max (1 + max _ _) _ ≤ _; unfold width; omega))
def output : Representation w (Reply config × config.handler.store.Value) := (reply config).prod (stored config)
  (fits config (by change 1 + max (1 + max _ _) _ + _ ≤ _; unfold width; omega))
def innerFinished := (innerReply config).prod (stored config)
  (fits config (by change 1 + max _ _ + _ ≤ _; unfold width; omega))

def innerReplyView : (Random.output config).Value ⊕ (Hash.output config).Value →
    ((Random.reply config).Value × config.handler.store.Value) ⊕
      (config.handler.sampler.tape.scalar.Value × config.handler.store.Value)
  | .inl value => .inl (productView (Random.reply config) config.handler.store value)
  | .inr value => .inr (productView config.handler.sampler.tape.scalar config.handler.store value)
def innerFinishedValue (value : (Random.output config).Value ⊕ (Hash.output config).Value) :=
  SumContext.view.symm (innerReplyView config value)
def innerFinish : Realizer .unit (Handler.innerOutput config) (innerFinished config) (innerFinishedValue config) :=
  ((SumContext.merge (randomReply config) (hashReply config) (stored config) config.sampler.wordFits (innerFinished config).fits).viewInput
    (Handler.innerOutput config) (innerReplyView config) (by intro value; cases value <;> rfl)).viewOutput
      (innerFinished config) (innerFinishedValue config) (fun _ => rfl)

def finished : Handler.Output config → Reply config × config.handler.store.Value
  | .inl value => (.inl (innerFinishedValue config value).1, (innerFinishedValue config value).2)
  | .inr value =>
      let pair := productView config.handler.core.reply config.handler.store value
      (.inr pair.1, pair.2)
def finish : Realizer .unit (Handler.output config) (output config) (finished config) :=
  (branchRealizer .unit (by decide) (Handler.innerOutput config) config.handler.output.representation (output config)
    ((innerFinish config).then (SumContext.mergeLeft (innerReply config) (signingReply config) (stored config)
      config.sampler.wordFits (output config).fits))
    ((SumContext.mergeRight (innerReply config) (signingReply config) (stored config)
      config.sampler.wordFits (output config).fits).viewInput config.handler.output.representation
        (productView config.handler.core.reply config.handler.store) (fun _ => rfl))
    config.sampler.wordFits (Handler.output config).fits).viewOutput (output config) (finished config)
      (by intro value; cases value <;> rfl)

end Signatures.Runtime.CaliperBackend.SchnorrROM.CallerPackets
