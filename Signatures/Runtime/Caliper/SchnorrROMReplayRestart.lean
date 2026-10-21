import Signatures.Runtime.Caliper.SchnorrROMTapeRestart
import Signatures.Runtime.Caliper.ByteRoute
import Signatures.Runtime.Caliper.ListNarrow
import Signatures.Runtime.SchnorrRawTapeBounds

/-! Restart into the original pass tape capacity. A reserved cell guarantees
that reset fits; executed copies remove the extra padding in both output lists.
The saved and remaining tapes are distinct stored copies of the reset prefix. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.ReplayRestart
open Caliper BoundedSource ByteRoute
variable {w : Nat} {F : Type} (layout : Layouts w F)

def input := (Restart.input layout).restrict (fun value => value.2.2.1.length < layout.capacity)
def smallReplay := layout.replay.restrict (fun state =>
  state.saved.length ≤ layout.capacity ∧ state.remaining.length ≤ layout.capacity)
def tapes (state : Schnorr.RawTape.State F) := (state.saved, state.remaining)
def narrowValue (value : (smallReplay layout).Value) : (Read.tapes layout).Value :=
  ⟨tapes value.val, ⟨value.property.2.1, value.property.1.1.2⟩, value.property.2.2, value.property.1.2.2⟩
def parts : List (Part w) :=
  [.slice 0 (Read.list layout).representation.encoding.words,
   .slice (layout.list (layout.capacity + 1) (by omega)).representation.encoding.words (Read.list layout).representation.encoding.words]
theorem parts_valid : Valid (smallReplay layout).representation.encoding.words (parts layout) := by
  change 0 + (1 + layout.capacity * layout.entry.representation.encoding.words) ≤
      (1 + (layout.capacity + 1) * layout.entry.representation.encoding.words) +
        (1 + (layout.capacity + 1) * layout.entry.representation.encoding.words) ∧
    (1 + (layout.capacity + 1) * layout.entry.representation.encoding.words) +
      (1 + layout.capacity * layout.entry.representation.encoding.words) ≤
      (1 + (layout.capacity + 1) * layout.entry.representation.encoding.words) +
        (1 + (layout.capacity + 1) * layout.entry.representation.encoding.words) ∧ True
  exact ⟨by nlinarith, by nlinarith, trivial⟩
theorem parts_size : words (parts layout) = (Read.tapes layout).representation.encoding.words := by
  change _ + (_ + 0) = _ + _
  omega
theorem parts_bytes (value : (smallReplay layout).Value) :
    bytes ((smallReplay layout).representation.encoding.encode value) (parts layout) =
      (Read.tapes layout).representation.encoding.encode (narrowValue layout value) := by
  let grown := layout.list (layout.capacity + 1) (by omega)
  let savedBytes := grown.representation.encoding.encode ⟨value.val.saved, value.property.1.1⟩
  let remainingBytes := grown.representation.encoding.encode ⟨value.val.remaining, value.property.1.2⟩
  have leftLength : savedBytes.length = grown.representation.encoding.words := Encoding.encode_length _ _
  have smaller : (Read.list layout).representation.encoding.words ≤ savedBytes.length := by
    rw [leftLength]
    change 1 + layout.capacity * layout.entry.representation.encoding.words ≤
      1 + (layout.capacity + 1) * layout.entry.representation.encoding.words
    nlinarith
  have leftBytes := Encoding.boundedList_take layout.entry.representation.encoding (layout.capacity + 1) layout.capacity
    (by omega) layout.countFits (listView layout.entry (layout.capacity + 1) ⟨value.val.saved, value.property.1.1⟩)
      (by simpa [listView] using value.property.2.1)
  have rightBytes := Encoding.boundedList_take layout.entry.representation.encoding (layout.capacity + 1) layout.capacity
    (by omega) layout.countFits (listView layout.entry (layout.capacity + 1) ⟨value.val.remaining, value.property.1.2⟩)
      (by simpa [listView] using value.property.2.2)
  change savedBytes.take (1 + layout.capacity * layout.entry.representation.encoding.words) =
    (Read.list layout).representation.encoding.encode ⟨value.val.saved, value.property.2.1, value.property.1.1.2⟩ at leftBytes
  change remainingBytes.take (1 + layout.capacity * layout.entry.representation.encoding.words) =
    (Read.list layout).representation.encoding.encode ⟨value.val.remaining, value.property.2.2, value.property.1.2.2⟩ at rightBytes
  change bytes (savedBytes ++ remainingBytes) (parts layout) = _
  simp only [parts, bytes, List.drop_zero, List.append_nil]
  rw [List.take_append_of_le_length smaller, List.drop_left' leftLength]
  change savedBytes.take (1 + layout.capacity * layout.entry.representation.encoding.words) ++
      remainingBytes.take (1 + layout.capacity * layout.entry.representation.encoding.words) = _
  rw [leftBytes, rightBytes]
  rfl

def narrow : Realizer .unit (smallReplay layout).representation (Read.tapes layout).representation (narrowValue layout) :=
  ByteRoute.realizer _ _ _ (parts layout) layout.wordFits (parts_valid layout) (parts_size layout) (parts_bytes layout)
def narrowing : Implementation .unit (smallReplay layout) (Read.tapes layout) tapes where
  preserves value valid := (narrowValue layout ⟨value, valid⟩).property
  program := narrow layout
theorem narrowing_bounded : (narrowing layout).BoundedBy (8 * (Read.tapes layout).representation.encoding.words)
    (26 * (Read.tapes layout).representation.encoding.words + 14) := by
  constructor
  · change ∀ value, (narrow layout).time value ≤ _
    exact ByteRoute.time _ _ _ _ _ _ _ _
  · change descriptionWords (narrow layout).code ≤ _
    exact ByteRoute.codeWords _ _ _ _ _ _ _ _

theorem reset_fits (value : Restart.Input F) (valid : (input layout).valid value) :
    (Restart.source value).saved.length ≤ layout.capacity ∧ (Restart.source value).remaining.length ≤ layout.capacity := by
  have growth := Schnorr.RawTape.restart_length value.1 value.2.1 ⟨value.2.2.1, value.2.2.2⟩
  change (Restart.source value).saved.length ≤ value.2.2.1.length + 1 ∧
    (Restart.source value).remaining = (Restart.source value).saved at growth
  have room := valid.2
  rw [growth.2]
  exact ⟨by omega, by omega⟩
def admitted : Implementation .unit (input layout) (smallReplay layout) Restart.source :=
  ((Restart.implementation layout).restrictInput (fun value => value.2.2.1.length < layout.capacity)).restrictOutput
    (fun state => state.saved.length ≤ layout.capacity ∧ state.remaining.length ≤ layout.capacity) (reset_fits layout)
def source (value : Restart.Input F) := tapes (Restart.source value)
def implementation : Implementation .unit (input layout) (Read.tapes layout) source :=
  (admitted layout).then (narrowing layout)
def timeBudget := Restart.timeBudget layout + 8 * (Read.tapes layout).representation.encoding.words
def codeBudget := Restart.codeBudget layout + 26 * (Read.tapes layout).representation.encoding.words + 15
theorem bounded : (implementation layout).BoundedBy (timeBudget layout) (codeBudget layout) := by
  have first := ((Restart.bounded layout).restrictInput (fun value => value.2.2.1.length < layout.capacity)).restrictOutput
    (fun state => state.saved.length ≤ layout.capacity ∧ state.remaining.length ≤ layout.capacity) (reset_fits layout)
  apply (first.then (narrowing_bounded layout)).mono
  · exact le_rfl
  · unfold codeBudget
    omega
theorem buffers : (implementation layout).program.code.memBound ≤ 6 := by
  have narrowed : (narrow layout).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
  exact max_le (Restart.buffers layout) (narrowed.trans (by decide))
theorem names (slots : Nat) : NamesAccounted (implementation layout).program.code slots := by
  have narrowed : NamesAccounted (narrow layout).code slots := ByteRoute.names _ _ _ _ _ _ _ _ slots
  exact ((Restart.constructed layout).names slots).seq narrowed

theorem source_rawInput (slot : Nat) (answer : F) (state : Schnorr.RawTape.State F) :
    source (Restart.rawInput slot answer state) = tapes (Schnorr.RawTape.restart slot answer state) := rfl

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.ReplayRestart
