import Proofs.Runtime.Caliper.SchnorrROMReplayFirstSource
import Proofs.Runtime.Caliper.SchnorrROMEnumeratedDraw

/-! A fresh public challenge draw with the selected slot and complete first
result retained in machine memory. Repacking the scalar and slot is charged. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayChallenge
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec ByteRoute
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

abbrev Input := config.handler.sampler.tape.counter.Value × Terminal.Output config
def input := config.handler.sampler.tape.counter.representation.prod (ReplaySecond.first config)
  (ReplaySecond.combinedFits config (by change 1 + _ ≤ _; omega))
def heldInput := config.handler.sampler.tape.unit.representation.prod (input config)
  (by change 0 + _ < _; have := (input config).fits; omega)
def heldOutput := config.handler.sampler.tape.scalar.representation.prod (input config)
  (ReplaySecond.combinedFits config (by change 1 + (1 + _) ≤ _; omega))
def heldCode := Interactive.retain (PrivateSampler.Enumerated.Direct.code config.sampler)
  (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape) (PrivateSampler.Enumerated.Direct.code config.sampler))
  0 1 (input config).encoding.words
def heldSource (value : Input config) :=
  (fun replacement => (replacement, value)) <$> PrivateSampler.Enumerated.Direct.source config.sampler

theorem held_refines : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit
    (input config) (heldOutput config) (heldSource config) (heldCode config) := by
  have kept := (PrivateSampler.Enumerated.Direct.refines config.sampler).retain (by decide) (input config)
    config.sampler.wordFits (heldInput config).fits (heldOutput config).fits
  exact kept.viewInput (input config) (fun value => (⟨(), trivial⟩, value)) (fun _ => rfl)

def repackValue (value : config.handler.sampler.tape.scalar.Value × Input config) : ReplaySecond.Request config :=
  ((value.2.1, value.1), value.2.2)
def repackParts : List (Part w) :=
  [.slice 1 1, .slice 0 1, .slice 2 (ReplaySecond.first config).encoding.words]
theorem repack_valid : Valid (heldOutput config).encoding.words (repackParts config) := by
  change (1 + 1 ≤ 1 + (1 + _)) ∧ (0 + 1 ≤ 1 + (1 + _)) ∧ (2 + _ ≤ 1 + (1 + _)) ∧ True
  exact ⟨by omega, by omega, by omega, trivial⟩
theorem repack_size : words (repackParts config) = (ReplaySecond.rawInput config).encoding.words := by
  change 1 + (1 + (_ + 0)) = (1 + 1) + _
  omega
theorem repack_bytes (value : config.handler.sampler.tape.scalar.Value × Input config) :
    bytes ((heldOutput config).encoding.encode value) (repackParts config) =
      (ReplaySecond.rawInput config).encoding.encode (repackValue config value) := by
  let replacement := config.handler.sampler.tape.scalar.representation.encoding.encode value.1
  let slot := config.handler.sampler.tape.counter.representation.encoding.encode value.2.1
  let first := (ReplaySecond.first config).encoding.encode value.2.2
  have replacementLength : replacement.length = 1 := Encoding.encode_length _ _
  have slotLength : slot.length = 1 := Encoding.encode_length _ _
  have firstLength : first.length = (ReplaySecond.first config).encoding.words := Encoding.encode_length _ _
  have one := slice_block replacement slot first
  have two := slice_block [] replacement (slot ++ first)
  have three := slice_block (replacement ++ slot) first []
  simp only [List.length_append, replacementLength, slotLength, firstLength, List.length_nil,
    List.nil_append, List.append_nil, List.append_assoc] at one two three
  change bytes (replacement ++ (slot ++ first)) (repackParts config) = (slot ++ replacement) ++ first
  simp only [repackParts, bytes, List.append_nil]
  rw [one, two, three, List.append_assoc]
def repack : Realizer .unit (heldOutput config) (ReplaySecond.rawInput config) (repackValue config) :=
  ByteRoute.realizer _ _ _ (repackParts config) config.sampler.wordFits
    (repack_valid config) (repack_size config) (repack_bytes config)
def program : Interactive.Code w := .seq (heldCode config) (.compute (repack config).code)
def source (value : Input config) :=
  (fun replacement => ((value.1, replacement), value.2)) <$> PrivateSampler.Enumerated.Direct.source config.sampler

theorem refines : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit
    (input config) (ReplaySecond.rawInput config) (source config) (program config) := by
  have joined := (held_refines config).seq
    (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (repack config))
  have sourceEq (value : Input config) :
      (do let drawn ← heldSource config value; pure (repackValue config drawn)) = source config value := by
    simp only [heldSource, ReplayChallenge.source]
    rfl
  intro tape value before holds
  change Synchronizes _ (source config value) _
  rw [← sourceEq value]
  exact joined tape value before holds

theorem retains_first (value : Input config) (answer) (reached : answer ∈ support (source config value)) :
    answer.2 = value.2 ∧ answer.1.1 = value.1 := by
  simp only [ReplayChallenge.source, support_map, Set.mem_image] at reached
  obtain ⟨_, _, rfl⟩ := reached
  exact ⟨rfl, rfl⟩

theorem uniform (value : Input config) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    (fun request => request.1.2.val) <$> source config value = ($ᵗ F : ProbComp F) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  unfold ReplayChallenge.source
  rw [Functor.map_map]
  exact PrivateSampler.Enumerated.Direct.uniform config.sampler

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayChallenge
