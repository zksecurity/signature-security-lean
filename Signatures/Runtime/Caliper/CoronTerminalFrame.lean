import Signatures.Runtime.Caliper.CoronTerminalBounds
import Signatures.Runtime.Caliper.BLSCallerPostcondition

/-! Construct the terminal input from an ordinary forgery and the complete
caller store. The generated instructions copy the message, cache, signature
and challenge point, emit the encoded fallback, and discard the unused logs
and challenge points. No mathematical tuple construction is a machine step. -/
namespace Signatures.Runtime.CaliperBackend.CoronTerminalFrame
open Caliper BoundedSource Assembly
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G : Type}
    (layout : CoronService.Layouts w M F G randomBound qS)

def forgery : Layout w (M × G) := layout.cache.key.prod layout.point
  (layout.service.fits_of_le (by
    have cacheWidth := layout.service.lookup_width
    unfold BLSReply.Layouts.width
    change layout.cache.key.representation.encoding.words + layout.point.representation.encoding.words ≤
      16 * (layout.service.cache.lookup.width + _ + layout.point.representation.encoding.words + _)
    change layout.service.cache.lookup.width = layout.cache.key.representation.encoding.words + _ + _ at cacheWidth
    omega))
abbrev Packet := (forgery layout).Value × layout.service.store.Value

def plain : Representation w (Packet layout) :=
  (forgery layout).representation.prod layout.service.store.representation
    (layout.service.fits_of_le (by
      have cacheWidth := layout.service.lookup_width
      rw [BLSReply.Layouts.store_words]
      change (layout.cache.key.representation.encoding.words + layout.point.representation.encoding.words) +
        (layout.service.config.representation.encoding.words + layout.service.cache.lookup.table.representation.encoding.words +
          2 * layout.service.logWords) ≤ _
      unfold BLSReply.Layouts.width
      change layout.service.cache.lookup.width = layout.cache.key.representation.encoding.words + _ + _ at cacheWidth
      change _ ≤ 16 * (layout.service.cache.lookup.width + layout.service.config.representation.encoding.words +
        layout.point.representation.encoding.words + 2 * layout.service.logWords)
      omega))

theorem plain_words : (plain layout).encoding.words = layout.cache.key.representation.encoding.words +
    4 * layout.point.representation.encoding.words + layout.service.cache.lookup.table.representation.encoding.words +
      2 * layout.service.logWords := by
  change (layout.cache.key.representation.encoding.words + layout.point.representation.encoding.words) +
    ((layout.point.representation.encoding.words + (layout.point.representation.encoding.words + layout.point.representation.encoding.words)) +
      (layout.service.cache.lookup.table.representation.encoding.words +
        (layout.service.logWords + layout.service.logWords))) = _
  omega

variable [DecidableEq M] (default : layout.cache.value.Value)
def ready (value : Packet layout) : Prop :=
  layout.service.cache.admissible (value.1.val.1, (layout.pairDefault default).val, value.2.val.2.1, ())
instance : DecidablePred (ready layout default) := fun _ => inferInstanceAs (Decidable (layout.service.cache.admissible _))
def input : Layout w (Packet layout) where
  valid := ready layout default
  representation := (plain layout).restrict (ready layout default)

def prepared (value : (input layout default).Value) : (CoronTerminal.input layout).Value :=
  ⟨((value.val.1.val.1, (layout.pairDefault default).val, value.val.2.val.2.1, ()),
      (value.val.1.val.2, value.val.2.val.1.2.1)),
    ⟨⟨value.val.1.property.1, (layout.pairDefault default).property, value.val.2.property.2.1, trivial⟩, value.property⟩,
      value.val.1.property.2, value.val.2.property.1.2.1⟩

def operands : List (Operand w) :=
  reads 0 0 layout.cache.key.representation.encoding.words ++
    (layout.service.cache.value.representation.encoding.encode (layout.pairDefault default)).map Operand.literal ++
    reads 0 (layout.cache.key.representation.encoding.words + layout.point.representation.encoding.words +
      layout.point.representation.encoding.words + layout.point.representation.encoding.words + layout.point.representation.encoding.words)
      layout.service.cache.lookup.table.representation.encoding.words ++
    reads 0 layout.cache.key.representation.encoding.words layout.point.representation.encoding.words ++
    reads 0 (layout.cache.key.representation.encoding.words + layout.point.representation.encoding.words +
      layout.point.representation.encoding.words) layout.point.representation.encoding.words

theorem operands_length : (operands layout default).length = (CoronTerminal.input layout).representation.encoding.words := by
  simp only [operands, List.length_append, List.length_map, reads_length, Encoding.encode_length]
  change _ = (layout.cache.key.representation.encoding.words +
    (layout.service.cache.value.representation.encoding.words + (layout.service.cache.lookup.table.representation.encoding.words + 0))) +
    (layout.point.representation.encoding.words + layout.point.representation.encoding.words)
  omega
omit [DecidableEq M] in
theorem operands_sources : SourcesBound (operands layout default) 1 := by
  intro operand member
  simp only [operands, List.mem_append] at member
  rcases member with (((member | member) | member) | member) | member
  all_goals first
    | exact sourcesBound_reads 0 _ _ 1 (by decide) operand member
    | obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial
omit [DecidableEq M] in
theorem operands_fit : ∀ operand ∈ operands layout default, operand.NamesFit := by
  intro operand member
  simp only [operands, List.mem_append] at member
  rcases member with (((member | member) | member) | member) | member
  all_goals first
    | exact reads_namesFit 0 _ _ (by positivity) operand member
    | obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial

def route : Realizer .unit (input layout default).representation (CoronTerminal.input layout).representation (prepared layout default) :=
  Assembly.realizer .unit (by decide) _ _ _ (operands layout default) layout.cache.wordFits
    (operands_length layout default) (operands_fit layout default)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = (plain layout).encoding.words at size
      have fits : (before.bufs 0).size < 2 ^ w := size ▸ (plain layout).fits
      rw [plain_words] at size
      simp only [operands, List.mem_append] at member
      rcases member with (((member | member) | member) | member) | member
      all_goals first
        | exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
        | obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial)
    (by
      intro value before represented
      let message := layout.cache.key.representation.encoding.encode ⟨value.val.1.val.1, value.val.1.property.1⟩
      let signature := layout.point.representation.encoding.encode ⟨value.val.1.val.2, value.val.1.property.2⟩
      let g := layout.point.representation.encoding.encode ⟨value.val.2.val.1.1, value.val.2.property.1.1⟩
      let X := layout.point.representation.encoding.encode ⟨value.val.2.val.1.2.1, value.val.2.property.1.2.1⟩
      let h := layout.point.representation.encoding.encode ⟨value.val.2.val.1.2.2, value.val.2.property.1.2.2⟩
      let cache := layout.service.cache.lookup.table.representation.encoding.encode ⟨value.val.2.val.2.1, value.val.2.property.2.1⟩
      let logs := layout.service.records.transcript.representation.encoding.encode ⟨value.val.2.val.2.2, value.val.2.property.2.2⟩
      have contents : (before.bufs 0).toList = (message ++ signature) ++ ((g ++ (X ++ h)) ++ (cache ++ logs)) := represented.2.1
      have messageRead := ListFold.reads_block [] message (signature ++ g ++ X ++ h ++ cache ++ logs) before
        (by simpa only [List.nil_append, List.append_assoc] using contents)
      have cacheRead := ListFold.reads_block (message ++ signature ++ g ++ X ++ h) cache logs before
        (by simpa only [List.append_assoc] using contents)
      have signatureRead := ListFold.reads_block message signature (g ++ X ++ h ++ cache ++ logs) before
        (by simpa only [List.append_assoc] using contents)
      have challengeRead := ListFold.reads_block (message ++ signature ++ g) X (h ++ cache ++ logs) before
        (by simpa only [List.append_assoc] using contents)
      simp only [List.length_nil, List.length_append, message, signature, g, X, h, cache, Encoding.encode_length]
        at messageRead cacheRead signatureRead challengeRead
      change values (operands layout default) before =
        (message ++ (layout.service.cache.value.representation.encoding.encode (layout.pairDefault default) ++ (cache ++ []))) ++
          (signature ++ X)
      simp only [operands, values, List.map_append, List.map_map, Function.comp_def, Operand.value]
        at messageRead cacheRead signatureRead challengeRead ⊢
      rw [messageRead, cacheRead, signatureRead, challengeRead]
      simp only [List.append_nil, List.append_assoc]
      change message ++ (List.map id (layout.service.cache.value.representation.encoding.encode (layout.pairDefault default)) ++
        (cache ++ (signature ++ X))) = _
      rw [List.map_id])

theorem route_time (value) : (route layout default).time value ≤ 8 * (CoronTerminal.input layout).representation.encoding.words := by
  have bounded := Assembly.code_time_unit_le (operands layout default)
  rw [operands_length] at bounded
  exact bounded
theorem route_words : descriptionWords (route layout default).code ≤ 26 * (CoronTerminal.input layout).representation.encoding.words + 14 := by
  have bounded := Assembly.code_descriptionWords_le (operands layout default)
  rw [operands_length] at bounded
  exact bounded
theorem route_names (slots : Nat) : NamesAccounted (route layout default).code slots :=
  Assembly.code_namesAccounted _ slots (operands_sources layout default)

theorem ready_of_postcondition {fuel : Nat} {before after : layout.service.store.Value}
    (post : BLSCaller.Postcondition layout.service fuel before after)
    (room : before.val.2.1.length + fuel + 1 ≤ layout.service.cache.capacityPred + 1)
    (result : (forgery layout).Value) : ready layout default (result, after) := by
  have := post.cache
  intro _
  change after.val.2.1.length ≤ layout.service.cache.capacityPred
  omega

end Signatures.Runtime.CaliperBackend.CoronTerminalFrame
