import Proofs.Runtime.Caliper.BLSReplyReachability
import Proofs.Runtime.Caliper.InteractiveInvariantBounds

/-! Executed initialization of the BLS private store. The caller input and
configuration are copied from runtime data; every empty cache/log word is written
by an instruction. Capacity is bounded by the chosen layout, not message space. -/

namespace Signatures.Runtime.CaliperBackend.BLSInitialization
open Caliper BoundedSource Assembly

variable {w : Nat} {M R C G U : Type} (layout : BLSReply.Layouts w M R C G)

def empty : layout.cacheLogs.Value := ⟨([], [], []), by
  change (([] : List (M × R)).length ≤ layout.cache.capacityPred + 1 ∧ _) ∧ (_ ∧ _)
  exact ⟨⟨Nat.zero_le _, by simp⟩, ⟨Nat.zero_le _, by simp⟩, ⟨Nat.zero_le _, by simp⟩⟩⟩

def store (config : layout.config.Value) : layout.store.Value :=
  ⟨(config.val, (empty layout).val), config.property, (empty layout).property⟩

variable (caller : Representation w U)
    (fits : caller.encoding.words + layout.store.representation.encoding.words < 2 ^ w)

def input : Representation w (U × layout.config.Value) :=
  caller.prod layout.config.representation (by
    have bound := layout.store_words
    omega)

def output : Representation w (U × layout.store.Value) := caller.prod layout.store.representation fits

def initialized (value : U × layout.config.Value) : U × layout.store.Value :=
  (value.1, store layout value.2)

def operands : List (Operand w) := reads 0 0 (input layout caller fits).encoding.words ++
  ((layout.cacheLogs.representation.encoding.encode (empty layout)).map Operand.literal)

theorem operands_length : (operands layout caller fits).length = (output layout caller fits).encoding.words := by
  simp only [operands, List.length_append, reads_length, List.length_map, Encoding.encode_length]
  change (caller.encoding.words + layout.config.representation.encoding.words) + _ =
    caller.encoding.words + (layout.config.representation.encoding.words + _)
  omega

theorem output_bytes (value : U × layout.config.Value) :
    (output layout caller fits).encoding.encode (initialized layout value) =
      (input layout caller fits).encoding.encode value ++ layout.cacheLogs.representation.encoding.encode (empty layout) := by
  change caller.encoding.encode value.1 ++
    (layout.config.representation.encoding.encode value.2 ++ layout.cacheLogs.representation.encoding.encode (empty layout)) =
      (caller.encoding.encode value.1 ++ layout.config.representation.encoding.encode value.2) ++ _
  exact (List.append_assoc _ _ _).symm

def code : Realizer .unit (input layout caller fits) (output layout caller fits) (initialized layout) :=
  Assembly.realizer .unit (by decide) _ _ _ (operands layout caller fits) layout.cache.wordFits
    (operands_length layout caller fits)
    (by
      intro operand member
      rcases List.mem_append.mp member with read | literal
      · exact reads_namesFit _ _ _ (by have := layout.cache.wordFits; omega) operand read
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal
        trivial)
    (by
      intro value before represented operand member
      rcases List.mem_append.mp member with read | literal
      · exact reads_valid 1 0 0 _ before (by decide)
          (by rw [represented_size _ represented]; omega)
          (by rw [represented_size _ represented]; exact (input layout caller fits).fits) operand read
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal
        trivial)
    (by
      intro value before represented
      have copied := reads_values 0 0 (input layout caller fits).encoding.words before
        (by rw [represented_size _ represented]; omega)
      rw [represented.2.1] at copied
      rw [List.drop_zero, List.take_of_length_le ((input layout caller fits).encoding.encode_length value).le] at copied
      rw [output_bytes]
      simp only [operands, values, List.map_append, List.map_map]
      exact congrArg₂ List.append copied (List.map_id _))

theorem time (value) : (code layout caller fits).time value ≤ 8 * (output layout caller fits).encoding.words := by
  change (Assembly.code (operands layout caller fits)).staticTime .unit ≤ _
  simpa only [operands_length] using code_time_unit_le (operands layout caller fits)

theorem words : descriptionWords (code layout caller fits).code ≤ 26 * (output layout caller fits).encoding.words + 14 := by
  change descriptionWords (Assembly.code (operands layout caller fits)) ≤ _
  simpa only [operands_length] using code_descriptionWords_le (operands layout caller fits)

theorem sources : SourcesBound (operands layout caller fits) 1 := by
  apply (sourcesBound_append _ _ _).mpr
  refine ⟨sourcesBound_reads _ _ _ _ (by decide), ?_⟩
  intro operand member
  obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
  trivial

theorem names : NamesBound (code layout caller fits).code 3 := by
  have bounds := code_names (operands layout caller fits) 1 (sources layout caller fits)
  exact ⟨bounds.1, bounds.2.trans (by decide)⟩

theorem buffers : (code layout caller fits).code.memBound ≤ 2 :=
  (code_names (operands layout caller fits) 1 (sources layout caller fits)).2

theorem reserved (remaining : Nat) (cacheRoom : remaining ≤ layout.cache.capacityPred + 1)
    (logRoom : remaining ≤ layout.capacityPred + 1) (config : layout.config.Value) :
    BLSReply.Reserved layout remaining (store layout config).val := by
  refine ⟨config.property, ?_, ?_, by simpa only [store, empty, List.length_nil, Nat.zero_add] using cacheRoom,
    by simpa only [store, empty, List.length_nil, Nat.zero_add] using logRoom⟩
  · intro entry member
    cases member
  · constructor <;> intro entry member <;> cases member

section Source
variable (source : Layout w U)
    (sourceFits : source.representation.encoding.words + layout.store.representation.encoding.words < 2 ^ w)

def sourceInput : Layout w (U × C) := source.prod layout.config (input layout source.representation sourceFits).fits

def sourceOutput : Layout w (U × BLSReply.Store M R C G) := source.prod layout.store sourceFits

def implementation : Implementation .unit (sourceInput layout source sourceFits) (sourceOutput layout source sourceFits)
    (fun value => (value.1, value.2, [], [], [])) where
  preserves _ valid := ⟨valid.1, valid.2, (empty layout).property⟩
  program := ((code layout source.representation sourceFits).viewInput
    (sourceInput layout source sourceFits).representation (productView source layout.config) (fun _ => rfl)).viewOutput
      (sourceOutput layout source sourceFits).representation
      (fun value => ⟨(value.val.1, value.val.2, [], [], []), value.property.1, value.property.2, (empty layout).property⟩)
      (fun _ => rfl)

theorem implementation_bounded : (implementation layout source sourceFits).BoundedBy
    (8 * (sourceOutput layout source sourceFits).representation.encoding.words)
    (26 * (sourceOutput layout source sourceFits).representation.encoding.words + 14) :=
  ⟨fun value => time layout source.representation sourceFits ((productView source layout.config) value),
    words layout source.representation sourceFits⟩

theorem implementation_names : NamesBound (implementation layout source sourceFits).program.code 3 :=
  names layout source.representation sourceFits

theorem implementation_buffers : (implementation layout source sourceFits).program.code.memBound ≤ 2 :=
  buffers layout source.representation sourceFits

end Source
end Signatures.Runtime.CaliperBackend.BLSInitialization
