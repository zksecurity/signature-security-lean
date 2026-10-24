import Proofs.Runtime.Caliper.SchnorrAGMSigningShape
import Proofs.Runtime.BackendSchnorrAGMSigningDispatch

/-! Accepted signing physically drops the incoming lists, then wraps the
computed signature as the source scalar/singleton-group reply. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.SigningDispatch
open Caliper BoundedSource Assembly
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def project : Implementation .unit layout.raw layout.signing.signing.base (fun args => args.2.2) :=
  (Implementation.second (by decide) layout.points layout.tail layout.scheme.wordFits layout.raw.representation.fits).then
    (Implementation.second (by decide) layout.coefficientRows layout.signing.signing.base layout.scheme.wordFits layout.tail.representation.fits)
def accept : Realizer .unit layout.yes.representation (Signing.Sampling.input layout.signing).representation layout.acceptedValue :=
  ((project layout).program.viewInput layout.yes.representation (fun args => ⟨args.val, args.property.1.1⟩) (fun _ => rfl)).viewOutput
    (Signing.Sampling.input layout.signing).representation layout.acceptedValue (fun _ => rfl)
theorem project_bounded : (project layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  have bound := (Implementation.second_boundedBy layout.points layout.tail layout.scheme.wordFits layout.raw.representation.fits).then
    (Implementation.second_boundedBy layout.coefficientRows layout.signing.signing.base layout.scheme.wordFits layout.tail.representation.fits)
  apply bound.mono
  all_goals
    have parts := layout.parts
    have base := layout.base_le
    have tail : layout.tail.representation.encoding.words = layout.coefficientRows.representation.encoding.words +
        layout.signing.signing.base.representation.encoding.words := rfl
    omega
theorem accept_time (args : layout.yes.Value) : (accept layout).time args ≤ 16 * layout.width :=
  (project_bounded layout).time_le ⟨args.val, args.property.1.1⟩
theorem accept_words : descriptionWords (accept layout).code ≤ 52 * layout.width + 29 := (project_bounded layout).code_le
theorem accept_names (slots : Nat) : NamesAccounted (accept layout).code slots :=
  (Implementation.second_names layout.points layout.tail layout.scheme.wordFits layout.raw.representation.fits slots).seq
    (Implementation.second_names layout.coefficientRows layout.signing.signing.base layout.scheme.wordFits layout.tail.representation.fits slots)
theorem accept_buffers : (accept layout).code.memBound ≤ 2 :=
  max_le (Implementation.second_buffers (cost := .unit) (by decide) layout.points layout.tail layout.scheme.wordFits layout.raw.representation.fits)
    (Implementation.second_buffers (cost := .unit) (by decide) layout.coefficientRows layout.signing.signing.base layout.scheme.wordFits layout.tail.representation.fits)

variable [DecidableEq M] [DecidableEq G]
def wrapValue (args : (Signing.Programming.output layout.signing).Value) : layout.output.Value :=
  ⟨Signatures.Runtime.SchnorrAGM.Native.SigningDispatch.wrapValue args.val,
    ⟨args.property.1.2, by change [args.val.1.1].length ≤ 1; simp only [List.length_singleton, Nat.le_refl], by
      change ∀ point ∈ [args.val.1.1], layout.scheme.point.valid point
      intro point member; simp only [List.mem_singleton] at member; subst point; exact args.property.1.1⟩, args.property.2⟩
def wrapPoint (args : (Signing.Programming.output layout.signing).Value) : layout.scheme.point.Value := ⟨args.val.1.1, args.property.1.1⟩
def wrapScalar (args : (Signing.Programming.output layout.signing).Value) : layout.scheme.scalar.Value := ⟨args.val.1.2, args.property.1.2⟩
def wrapState (args : (Signing.Programming.output layout.signing).Value) : layout.scheme.state.Value := ⟨args.val.2, args.property.2⟩
theorem wrap_bytes (args : (Signing.Programming.output layout.signing).Value) :
    layout.output.representation.encoding.encode (wrapValue layout args) =
      (layout.scheme.scalar.representation.encoding.encode (wrapScalar layout args) ++
        [1] ++ layout.scheme.point.representation.encoding.encode (wrapPoint layout args)) ++
          layout.scheme.state.representation.encoding.encode (wrapState layout args) := by
  have singleton := ListBytes.singleton_bytes layout.scheme.point 1 (by have := layout.scheme.wordFits; omega)
    layout.replyPoints.representation.fits ⟨[args.val.1.1], (wrapValue layout args).property.1.2⟩ (wrapPoint layout args) rfl
  simp only [Nat.sub_self, Nat.zero_mul, List.replicate_zero, List.append_nil] at singleton
  exact (congrArg (fun bytes =>
    (layout.scheme.scalar.representation.encoding.encode (wrapScalar layout args) ++ bytes) ++
      layout.scheme.state.representation.encoding.encode (wrapState layout args)) singleton).trans
        (by simp only [List.append_assoc, List.singleton_append])

def wrapOperands : List (Operand w) :=
  reads 0 layout.scheme.point.representation.encoding.words layout.scheme.scalar.representation.encoding.words ++ [.literal 1] ++
    reads 0 0 layout.scheme.point.representation.encoding.words ++
      reads 0 (layout.scheme.point.representation.encoding.words + layout.scheme.scalar.representation.encoding.words)
        layout.scheme.state.representation.encoding.words
omit [DecidableEq M] [DecidableEq G] in
theorem wrapOperands_length : (wrapOperands layout).length = layout.output.representation.encoding.words := by
  simp only [wrapOperands, List.length_append, reads_length, List.length_cons, List.length_nil]
  change _ = (_ + (1 + 1 * _)) + _
  omega
omit [DecidableEq M] [DecidableEq G] in
theorem wrapOperands_sources : SourcesBound (wrapOperands layout) 1 := by
  simp only [wrapOperands, sourcesBound_append]
  refine ⟨⟨⟨sourcesBound_reads _ _ _ _ (by decide), ?_⟩, sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩
  intro operand member
  simp only [List.mem_singleton] at member
  subst operand
  trivial

def wrap : Realizer .unit (Signing.Programming.output layout.signing).representation layout.output.representation (wrapValue layout) :=
  Assembly.realizer .unit (by decide) _ _ _ (wrapOperands layout) layout.scheme.wordFits (wrapOperands_length layout)
    (by
      intro operand member
      simp only [wrapOperands, List.mem_append, List.mem_singleton] at member
      rcases member with ((copied | rfl) | copied) | copied
      · exact reads_namesFit 0 _ _ (by positivity) operand copied
      · trivial
      · exact reads_namesFit 0 _ _ (by positivity) operand copied
      · exact reads_namesFit 0 _ _ (by positivity) operand copied)
    (by
      intro args before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = (layout.scheme.point.representation.encoding.words + layout.scheme.scalar.representation.encoding.words) +
        layout.scheme.state.representation.encoding.words at size
      have fits : (before.bufs 0).size < 2 ^ w := by rw [represented_size _ represented]; exact (Signing.Programming.output layout.signing).representation.fits
      simp only [wrapOperands, List.mem_append, List.mem_singleton] at member
      rcases member with ((copied | rfl) | copied) | copied
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand copied
      · trivial
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand copied
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand copied)
    (by
      intro args before represented
      let pointBytes := layout.scheme.point.representation.encoding.encode (wrapPoint layout args)
      let scalarBytes := layout.scheme.scalar.representation.encoding.encode (wrapScalar layout args)
      let stateBytes := layout.scheme.state.representation.encoding.encode (wrapState layout args)
      have contents : (before.bufs 0).toList = (pointBytes ++ scalarBytes) ++ stateBytes := represented.2.1
      have scalar := ListFold.reads_block pointBytes scalarBytes stateBytes before contents
      have point := ListFold.reads_block [] pointBytes (scalarBytes ++ stateBytes) before (by simpa only [List.nil_append, List.append_assoc] using contents)
      have state := ListFold.reads_block (pointBytes ++ scalarBytes) stateBytes [] before (by simpa only [List.append_nil] using contents)
      simp only [pointBytes, scalarBytes, stateBytes, Encoding.encode_length, List.length_nil, List.length_append] at scalar point state
      rw [wrap_bytes]
      simp only [wrapOperands, values, List.map_append]
      change ((values (reads 0 _ _) before ++ [1]) ++ values (reads 0 _ _) before) ++ values (reads 0 _ _) before = _
      rw [scalar, point, state])

theorem wrap_time (args : (Signing.Programming.output layout.signing).Value) :
    (wrap layout).time args ≤ 8 * layout.output.representation.encoding.words := by
  have bound := code_time_unit_le (wrapOperands layout)
  rw [wrapOperands_length] at bound
  exact bound
theorem wrap_words : descriptionWords (wrap layout).code ≤ 26 * layout.output.representation.encoding.words + 14 := by
  have bound := code_descriptionWords_le (wrapOperands layout)
  rw [wrapOperands_length] at bound
  exact bound
theorem wrap_names (slots : Nat) : NamesAccounted (wrap layout).code slots := code_namesAccounted _ _ (wrapOperands_sources layout)
theorem wrap_buffers : (wrap layout).code.memBound ≤ 2 := (code_names _ _ (wrapOperands_sources layout)).2

end Signatures.Runtime.CaliperBackend.SchnorrAGM.SigningDispatch
