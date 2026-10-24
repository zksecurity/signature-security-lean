import Proofs.Runtime.Caliper.SchnorrROMReplayChallengeBounds
import Proofs.Runtime.Caliper.SchnorrROMFreshGuardBounds

/-! Apply the original public-cell rejection test to a replay request, retaining
that whole request for the second pass. Routing reads saved cells, never the
remaining tape or the final forgery challenge. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayChallenge.Guard
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec ByteRoute
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

def argument := (FreshGuard.input config.handler.sampler.tape).representation
def savedList := config.handler.sampler.tape.list config.handler.sampler.tape.capacity (by omega)
theorem first_parts : (ReplaySecond.first config).encoding.words = ReplaySecond.prefixWords config +
    ((savedList config).representation.encoding.words + (savedList config).representation.encoding.words) :=
  ReplaySecond.first_parts config
def prepared := (argument config).prod (ReplaySecond.rawInput config) (ReplaySecond.combinedFits config (by
  have parts := first_parts config
  change (1 + (1 + (savedList config).representation.encoding.words)) + ((1 + 1) + _) ≤ _
  omega))
def output := config.handler.sampler.tape.boolean.representation.prod (ReplaySecond.rawInput config)
  (ReplaySecond.combinedFits config (by change 1 + ((1 + 1) + _) ≤ _; omega))
def guardValue (value : ReplaySecond.Request config) : (FreshGuard.input config.handler.sampler.tape).Value :=
  ⟨(value.1.1.val, value.1.2.val, value.2.2.val.2.1), value.1.1.property, value.1.2.property, value.2.2.property.2.1⟩
def prepareParts : List (Part w) :=
  [.slice 0 (ReplaySecond.arguments config).encoding.words,
   .slice ((ReplaySecond.arguments config).encoding.words + ReplaySecond.prefixWords config) (savedList config).representation.encoding.words,
   .slice 0 (ReplaySecond.rawInput config).encoding.words]
theorem prepare_valid : Valid (ReplaySecond.rawInput config).encoding.words (prepareParts config) := by
  have parts := first_parts config
  change (0 + 2 ≤ 2 + _) ∧ (2 + ReplaySecond.prefixWords config + _ ≤ 2 + _) ∧
    (0 + (ReplaySecond.rawInput config).encoding.words ≤ (ReplaySecond.rawInput config).encoding.words) ∧ True
  exact ⟨by omega, by omega, by omega, trivial⟩
theorem prepare_size : ByteRoute.words (prepareParts config) = (prepared config).encoding.words := by
  change (1 + 1) + ((savedList config).representation.encoding.words + ((ReplaySecond.rawInput config).encoding.words + 0)) =
    (1 + (1 + (savedList config).representation.encoding.words)) + (ReplaySecond.rawInput config).encoding.words
  omega
theorem prepare_bytes (value : ReplaySecond.Request config) :
    bytes ((ReplaySecond.rawInput config).encoding.encode value) (prepareParts config) =
      (prepared config).encoding.encode (guardValue config value, value) := by
  let args := (ReplaySecond.arguments config).encoding.encode value.1
  let front := ReplaySecond.prefixBytes config value.2
  let saved := (savedList config).representation.encoding.encode ⟨value.2.2.val.2.1, value.2.2.property.2.1⟩
  let remaining := (savedList config).representation.encoding.encode ⟨value.2.2.val.2.2, value.2.2.property.2.2⟩
  let original := (ReplaySecond.rawInput config).encoding.encode value
  have argsLength : args.length = (ReplaySecond.arguments config).encoding.words := Encoding.encode_length _ _
  have prefixLength : front.length = ReplaySecond.prefixWords config := ReplaySecond.prefix_length config value.2
  have savedLength : saved.length = (savedList config).representation.encoding.words := Encoding.encode_length _ _
  have originalLength : original.length = (ReplaySecond.rawInput config).encoding.words := Encoding.encode_length _ _
  have split : original = args ++ (front ++ (saved ++ remaining)) := by
    change args ++ (ReplaySecond.first config).encoding.encode value.2 = _
    rw [ReplaySecond.first_bytes]
    rfl
  have one := slice_block [] args (front ++ (saved ++ remaining))
  have two := slice_block (args ++ front) saved remaining
  have three := slice_block [] original []
  simp only [List.length_nil, List.nil_append, List.append_nil, List.length_append,
    argsLength, prefixLength, savedLength, originalLength, List.append_assoc] at one two three
  rw [← split] at one two
  have encodedArgument : (argument config).encoding.encode (guardValue config value) = args ++ saved := by
    change _ ++ (_ ++ _) = (_ ++ _) ++ _
    rw [List.append_assoc]
    rfl
  change bytes original (prepareParts config) = (argument config).encoding.encode (guardValue config value) ++ original
  rw [encodedArgument]
  simp only [prepareParts, bytes, List.append_nil]
  rw [one, two, three, List.append_assoc]
def prepare : Realizer .unit (ReplaySecond.rawInput config) (prepared config) (fun value => (guardValue config value, value)) :=
  ByteRoute.realizer _ _ _ (prepareParts config) config.sampler.wordFits
    (prepare_valid config) (prepare_size config) (prepare_bytes config)

variable [DecidableEq F]
theorem savedNameFits : (FreshGuard.implementation config.handler.sampler.tape).program.savedBuffer < 2 ^ w := by
  have bound := FreshGuard.buffers config.handler.sampler.tape
  have room := config.sampler.wordFits
  unfold Realizer.savedBuffer
  omega
def retained := (FreshGuard.implementation config.handler.sampler.tape).program.retain (by decide) (ReplaySecond.rawInput config)
  config.sampler.wordFits (savedNameFits config) (prepared config).fits (output config).fits
def source (value : ReplaySecond.Request config) : config.handler.sampler.tape.boolean.Value × ReplaySecond.Request config :=
  (⟨FreshGuard.source (guardValue config value).val, trivial⟩, value)
def realizer : Realizer .unit (ReplaySecond.rawInput config) (output config) (source config) :=
  ((prepare config).then (retained config)).viewOutput (output config) (source config) (fun _ => rfl)
theorem names (slots : Nat) : NamesAccounted (realizer config).code slots :=
  (ByteRoute.names _ _ _ _ _ _ _ _ slots).seq (Retain.names (FreshGuard.names config.handler.sampler.tape slots) _ _ _)
theorem buffers : (realizer config).code.memBound ≤ 9 := by
  have prepared : (prepare config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
  have kept := (FreshGuard.implementation config.handler.sampler.tape).program.retain_buffers (by decide) (ReplaySecond.rawInput config)
    config.sampler.wordFits (savedNameFits config) (ReplayChallenge.Guard.prepared config).fits (output config).fits
  have body := FreshGuard.buffers config.handler.sampler.tape
  change (retained config).code.memBound ≤ _ at kept
  change max (prepare config).code.memBound (retained config).code.memBound ≤ _
  omega

theorem source_original [Zero F] (value : ReplaySecond.Request config) :
    (source config value).1.val = decide ((Schnorr.RawTape.values (.inr ()) value.2.2.val.2.1)[value.1.1.val]? = some value.1.2.val) :=
  FreshGuard.source_original (guardValue config value).val

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayChallenge.Guard
