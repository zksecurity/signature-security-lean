import Proofs.Runtime.Caliper.SchnorrAGMCallerFinishLayout

/-! Executed caller-to-terminal conversion. The program drops union padding
and the public configuration, and moves the response behind the private state.
The cache-admission restriction supplies only a proof, never a free data move. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerFinish
open Caliper BoundedSource Assembly
variable {w qH qS : Nat} {M F G P : Type} (layout : HashDispatch.Layouts w M F G qH qS)
    (pending : Representation w P)
    (fits : 1 + max (forgery layout).representation.encoding.words pending.encoding.words +
      layout.hash.scheme.store.representation.encoding.words < 2 ^ w)

def routeOperands : List (Operand w) :=
  reads 0 0 layout.hash.scheme.message.representation.encoding.words ++
    reads 0 (layout.hash.scheme.message.representation.encoding.words + layout.hash.scheme.scalar.representation.encoding.words)
      (layout.points.representation.encoding.words + layout.coefficients.representation.encoding.words) ++
    reads 0 (max (forgery layout).representation.encoding.words pending.encoding.words +
      layout.hash.scheme.config.representation.encoding.words) layout.hash.scheme.state.representation.encoding.words ++
    reads 0 layout.hash.scheme.message.representation.encoding.words layout.hash.scheme.scalar.representation.encoding.words
theorem route_sources : SourcesBound (routeOperands layout pending) 1 := by
  simp only [routeOperands, sourcesBound_append]
  exact ⟨⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩
theorem route_fit : ∀ operand ∈ routeOperands layout pending, operand.NamesFit := by
  intro operand member
  simp only [routeOperands, List.mem_append] at member
  rcases member with ((member | member) | member) | member <;>
    exact reads_namesFit 0 _ _ (by positivity) operand member

variable [DecidableEq M] [DecidableEq G]
theorem route_length : (routeOperands layout pending).length = (Extraction.input layout).representation.encoding.words := by
  simp only [routeOperands, List.length_append, reads_length]
  change _ = (layout.hash.scheme.message.representation.encoding.words +
    (layout.points.representation.encoding.words + (layout.coefficients.representation.encoding.words +
      layout.hash.scheme.state.representation.encoding.words))) + layout.hash.scheme.scalar.representation.encoding.words
  omega

def route : Realizer .unit ((returned layout pending fits).restrict (admitted layout))
    (Extraction.input layout).representation (extractInput layout) :=
  Assembly.realizer .unit (by decide) _ _ _ (routeOperands layout pending) layout.hash.scheme.wordFits
    (route_length layout pending) (route_fit layout pending)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = (returned layout pending fits).encoding.words at size
      rw [(frame_sizes layout pending fits).1] at size
      have forge := forgery_words layout
      have stored : layout.hash.scheme.store.representation.encoding.words =
          layout.hash.scheme.config.representation.encoding.words + layout.hash.scheme.state.representation.encoding.words := rfl
      have extent := (returned layout pending fits).fits
      rw [(frame_sizes layout pending fits).1] at extent
      simp only [routeOperands, List.mem_append] at member
      rcases member with ((member | member) | member) | member <;>
        exact reads_valid 1 0 _ _ before (by decide) (by omega) (by omega) operand member)
    (by
      intro value before represented
      let message := layout.hash.scheme.message.representation.encoding.encode ⟨value.val.1.val.1.1, value.val.1.property.1.1⟩
      let scalar := layout.hash.scheme.scalar.representation.encoding.encode ⟨value.val.1.val.1.2, value.val.1.property.1.2⟩
      let groups := layout.points.representation.encoding.encode ⟨value.val.1.val.2.1, value.val.1.property.2.1⟩
      let rows := layout.coefficients.representation.encoding.encode ⟨value.val.1.val.2.2, value.val.1.property.2.2⟩
      let padding := List.replicate (max (forgery layout).representation.encoding.words pending.encoding.words -
        (forgery layout).representation.encoding.words) (0 : Word w)
      let config := layout.hash.scheme.config.representation.encoding.encode ⟨value.val.2.val.1, value.val.2.property.1⟩
      let stored := layout.hash.scheme.state.representation.encoding.encode ⟨value.val.2.val.2, value.val.2.property.2⟩
      have contents : (before.bufs 0).toList = (((message ++ scalar) ++ (groups ++ rows)) ++ padding) ++ (config ++ stored) := represented.2.1
      have first := ListFold.reads_block [] message (scalar ++ groups ++ rows ++ padding ++ config ++ stored) before
        (by simpa only [List.nil_append, List.append_assoc] using contents)
      have second := ListFold.reads_block (message ++ scalar) (groups ++ rows) (padding ++ config ++ stored) before
        (by simpa only [List.append_assoc] using contents)
      have third := ListFold.reads_block (message ++ scalar ++ groups ++ rows ++ padding ++ config) stored [] before
        (by simpa only [List.append_nil, List.append_assoc] using contents)
      have last := ListFold.reads_block message scalar (groups ++ rows ++ padding ++ config ++ stored) before
        (by simpa only [List.append_assoc] using contents)
      have paddedLength : message.length + scalar.length + groups.length + rows.length + padding.length =
          max (forgery layout).representation.encoding.words pending.encoding.words := by
        simp only [message, scalar, groups, rows, padding, Encoding.encode_length, List.length_replicate]
        have := forgery_words layout
        omega
      simp only [List.length_append, paddedLength, List.length_nil] at first second third last
      simp only [message, scalar, groups, rows, config, stored, Encoding.encode_length] at first second third last
      change values (routeOperands layout pending) before = message ++ (groups ++ (rows ++ stored)) ++ scalar
      simp only [routeOperands, values, List.map_append]
      change values (reads 0 0 _) before ++ values (reads 0 _ _) before ++ values (reads 0 _ _) before ++ values (reads 0 _ _) before = _
      rw [first, second, third, last]
      simp only [message, scalar, groups, rows, stored, List.append_assoc])

theorem route_time (value) : (route layout pending fits).time value ≤ 8 * (Extraction.input layout).representation.encoding.words := by
  have bound := code_time_unit_le (routeOperands layout pending)
  rw [route_length] at bound
  exact bound
theorem route_words : descriptionWords (route layout pending fits).code ≤
    26 * (Extraction.input layout).representation.encoding.words + 14 := by
  have bound := code_descriptionWords_le (routeOperands layout pending)
  rw [route_length] at bound
  exact bound
theorem route_names (slots : Nat) : NamesAccounted (route layout pending fits).code slots :=
  code_namesAccounted _ slots (route_sources layout pending)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerFinish
