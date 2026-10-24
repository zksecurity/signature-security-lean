import Proofs.Runtime.Caliper.SchnorrROMTapeReplyBounds
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMTapeReply
open SchnorrROMTape

private def layout : Layouts 12 Nat where
  scalar := Layout.counter 12 4096 (by decide) (by decide)
  capacity := 6
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def saved : List (Schnorr.TapeCell Nat) := [(3, 0, 1), (1, 0, 0), (7, 0, 2)]
private def remaining : List (Schnorr.TapeCell Nat) := [(1, 22, 0)]
private def response (scalar natural : Fin 4096) : (Read.output layout).Value :=
  ⟨((0, scalar.val, natural.val), saved, remaining), by
    change (0 < 4096 ∧ scalar.val < 4096 ∧ natural.val < 4096) ∧
      (3 ≤ 6 ∧ ∀ cell ∈ saved, cell.1 < 4096 ∧ cell.2.1 < 4096 ∧ cell.2.2 < 4096) ∧
      (1 ≤ 6 ∧ ∀ cell ∈ remaining, cell.1 < 4096 ∧ cell.2.1 < 4096 ∧ cell.2.2 < 4096)
    simp [saved, remaining, scalar.isLt, natural.isLt]⟩
private def privateInput (range : Fin 4094) (natural : Fin 4096) : (Reply.input layout).Value :=
  ⟨(range.val, (response 123 natural).val), range.isLt, (response 123 natural).property⟩

private def run {A B : Type} {input : Layout 12 A} {output : Layout 12 B} {f : A → B}
    (body : Constructed input output f) (value : input.Value) :=
  let initial := input.representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 100000 body.implementation.program.code before).map fun result =>
    ((output.representation.encoding.decode (result.1.bufs 0).toList).map Subtype.val,
      result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
      (List.range 10).all (fun i => result.1.caps (i + 1) == 0))

private def modulo := Constructed.modulo 4096 4096 layout.wordFits (by decide) (by decide)
example : (Reply.privateDecoder layout).implementation.program.code.memBound ≤ 6 := by
  simpa only [Reply.private_buffers] using (Reply.privateDecoder layout).buffers_le
example : (Reply.scalarDecoder layout).implementation.program.code.memBound ≤ 3 := by
  simpa only [Reply.scalar_buffers] using (Reply.scalarDecoder layout).buffers_le
example : (Reply.privateDecoder layout).implementation.BoundedBy (Reply.privateTime layout) (Reply.privateWords layout) :=
  Reply.private_bounded layout
example : (Reply.scalarDecoder layout).implementation.BoundedBy (Reply.scalarTime layout) (Reply.scalarWords layout) :=
  Reply.scalar_bounded layout
example : ¬ (Reply.input layout).valid (4094, (response 0 0).val) := by
  intro valid
  have impossible : 4094 < 4094 := valid.1
  omega
example : ¬ (Reply.privateOutput layout).valid (7, 8, saved, remaining) := by
  intro valid
  have impossible : 8 ≤ 7 := valid.2
  omega

-- Deliberately oversized stored replies exercise the actual remainder.
-- No valid-cell premise or relation between the stored tag and range is used.
open Lean in
run_cmd do
  for (range, natural, expected) in [
      ((0 : Fin 4094), (4095 : Fin 4096), (0 : Nat)), (7, 10, 2), (7, 4095, 7),
      (7, 0, 0), (4093, 4095, 1), (4093, 4093, 4093)] do
    unless run (Reply.privateDecoder layout) (privateInput range natural) ==
        some (some (range.val, expected, saved, remaining), #[77], 4, 91, 9, true) do
      throwError "caller private decoder did not execute remainder or preserve both tapes at range {range.val}"
  for scalar in [(0 : Fin 4096), 99, 4095] do
    unless run (Reply.scalarDecoder layout) (response scalar 4095) ==
        some (some (scalar.val, saved, remaining), #[77], 4, 91, 9, true) do
      throwError "caller scalar decoder changed the scalar or replay state"
  for (dividend, divisor, expected) in [
      ((4095 : Fin 4096), (0 : Fin 4096), (4095 : Nat)), (4095, 1, 0),
      (4095, 4094, 1), (0, 0, 0)] do
    unless run modulo ⟨(dividend.val, divisor.val), dividend.isLt, divisor.isLt⟩ ==
        some (some expected, #[77], 4, 91, 9, true) do
      throwError "word remainder disagrees with natural remainder"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Constructed.add, ``Constructed.modulo, ``Reply.privateDecoder, ``Reply.scalarDecoder,
      ``Reply.private_source, ``Reply.scalar_source, ``Reply.private_bounded, ``Reply.scalar_bounded,
      ``Reply.private_resources, ``Reply.scalar_resources] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMTapeReply
