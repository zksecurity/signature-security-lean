import Signatures.Runtime.Caliper.WeightedExtractorMemory
import Signatures.Runtime.Caliper.SumContextBounds

/-! A caller exit includes a tagged result, union padding, configuration and
private store. The successful route copies the forgery and private store into
the extractor input, dropping the configuration only by executing instructions.
The cutoff route is represented explicitly and receives no extraction premise. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCallerFinish
open Caliper BoundedSource Assembly
variable {w : Nat} {K M G F R C P : Type}
    (layout : WeightedExtractor.Layouts w K M G F R)
    (config : Representation w C) (pending : Representation w P)
    (fits : 1 + max layout.forgery.representation.encoding.words pending.encoding.words +
      config.encoding.words + layout.store.representation.encoding.words < 2 ^ w)

abbrev Forgery := layout.forgery.Value
abbrev Store := layout.store.Value
abbrev Packet := (Forgery layout ⊕ P) × (C × Store layout)

def saved : Representation w (C × Store layout) := config.prod layout.store.representation (by omega)
def input : Representation w (Packet (P := P) (C := C) layout) :=
  SumContext.input layout.forgery.representation pending (saved layout config pending fits)
    layout.signing.rows.accumulation.cache.wordFits (by change 1 + max _ _ + (_ + _) < _; omega)
def returned : Representation w (Forgery layout × (C × Store layout)) :=
  SumContext.leftFrame layout.forgery.representation pending (saved layout config pending fits)
    (by change 1 + max _ _ + (_ + _) < _; omega)
def cutoff : Representation w (P × (C × Store layout)) :=
  SumContext.rightFrame layout.forgery.representation pending (saved layout config pending fits)
    (by change 1 + max _ _ + (_ + _) < _; omega)

def extractInput (value : Forgery layout × (C × Store layout)) : layout.input.Value :=
  ⟨(value.1.val, value.2.2.val), value.1.property, value.2.2.property⟩

def routeOperands : List (Operand w) :=
  reads 0 0 layout.forgery.representation.encoding.words ++
    reads 0 (max layout.forgery.representation.encoding.words pending.encoding.words + config.encoding.words)
      layout.store.representation.encoding.words
theorem route_length : (routeOperands layout config pending).length = layout.input.representation.encoding.words := by
  simp only [routeOperands, List.length_append, reads_length]; rfl
theorem route_sources : SourcesBound (routeOperands layout config pending) 1 :=
  (sourcesBound_append _ _ _).mpr ⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩
theorem route_fit : ∀ operand ∈ routeOperands layout config pending, operand.NamesFit := by
  intro operand member
  rcases List.mem_append.mp member with member | member <;>
    exact reads_namesFit 0 _ _ (by positivity) operand member

def route : Realizer .unit (returned layout config pending fits)
    layout.input.representation (extractInput layout) :=
  Assembly.realizer .unit (by decide) _ _ _ (routeOperands layout config pending)
    layout.signing.rows.accumulation.cache.wordFits (route_length layout config pending) (route_fit layout config pending)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size =
        (layout.forgery.representation.encoding.words +
          (max layout.forgery.representation.encoding.words pending.encoding.words -
            layout.forgery.representation.encoding.words)) +
          (config.encoding.words + layout.store.representation.encoding.words) at size
      rcases List.mem_append.mp member with member | member <;>
        exact reads_valid 1 0 _ _ before (by decide) (by omega) (by omega) operand member)
    (by
      intro value before represented
      let forgery := layout.forgery.representation.encoding.encode value.1
      let padding := List.replicate
        (max layout.forgery.representation.encoding.words pending.encoding.words -
          layout.forgery.representation.encoding.words) (0 : Word w)
      let configuration := config.encoding.encode value.2.1
      let stored := layout.store.representation.encoding.encode value.2.2
      have contents : (before.bufs 0).toList = (forgery ++ padding) ++ (configuration ++ stored) := represented.2.1
      have first := ListFold.reads_block [] forgery (padding ++ configuration ++ stored) before
        (by simpa only [List.nil_append, List.append_assoc] using contents)
      have last := ListFold.reads_block (forgery ++ padding ++ configuration) stored [] before
        (by simpa only [List.append_nil, List.append_assoc] using contents)
      have lengths : forgery.length + padding.length = max
          layout.forgery.representation.encoding.words pending.encoding.words := by
        simp only [forgery, padding, Encoding.encode_length, List.length_replicate]; omega
      simp only [List.length_nil, List.length_append, lengths] at first last
      simp only [forgery, configuration, stored, Encoding.encode_length] at first last
      change values (routeOperands layout config pending) before = forgery ++ stored
      simp only [routeOperands, values, List.map_append] at first last ⊢
      exact congrArg₂ List.append first last)

theorem route_time (value) : (route layout config pending fits).time value ≤
    8 * layout.input.representation.encoding.words := by
  have bound := Assembly.code_time_unit_le (routeOperands layout config pending)
  rw [route_length] at bound
  exact bound
theorem route_words : descriptionWords (route layout config pending fits).code ≤
    26 * layout.input.representation.encoding.words + 14 := by
  have bound := Assembly.code_descriptionWords_le (routeOperands layout config pending)
  rw [route_length] at bound
  exact bound
theorem route_names (slots : Nat) : NamesAccounted (route layout config pending fits).code slots :=
  Assembly.code_namesAccounted _ slots (route_sources layout config pending)

theorem frame_sizes : (returned layout config pending fits).encoding.words =
      max layout.forgery.representation.encoding.words pending.encoding.words +
        config.encoding.words + layout.store.representation.encoding.words ∧
    (cutoff layout config pending fits).encoding.words = (returned layout config pending fits).encoding.words := by
  have sizes := SumContext.frame_words layout.forgery.representation pending (saved layout config pending fits)
    (by change 1 + max _ _ + (_ + _) < _; omega)
  have left := sizes.1
  change (returned layout config pending fits).encoding.words =
    max layout.forgery.representation.encoding.words pending.encoding.words +
      (config.encoding.words + layout.store.representation.encoding.words) at left
  exact ⟨by simpa only [Nat.add_assoc] using left, sizes.2.trans sizes.1.symm⟩

theorem choice_fits : 1 + max (returned layout config pending fits).encoding.words (cutoff layout config pending fits).encoding.words < 2 ^ w := by
  rw [(frame_sizes layout config pending fits).2, max_self, (frame_sizes layout config pending fits).1]
  omega
theorem input_bytes (value : Packet (P := P) (C := C) layout) :
    ((returned layout config pending fits).sum (cutoff layout config pending fits) (width_pos layout.signing.rows.accumulation.cache.wordFits)
      (choice_fits layout config pending fits)).encoding.encode (SumContext.view value) =
        (input layout config pending fits).encoding.encode value :=
  SumContext.sameBytes layout.forgery.representation pending (saved layout config pending fits)
    layout.signing.rows.accumulation.cache.wordFits _ value
end Signatures.Runtime.CaliperBackend.WeightedCallerFinish
