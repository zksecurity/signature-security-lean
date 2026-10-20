import Signatures.Runtime.Caliper.SchnorrAGMRandomShape
import Signatures.Runtime.BackendSchnorrAGMRandom

/-! Marking malformed randomness requests updates exactly one canonical flag
word. Cache, histories, range and bad flag retain their stored bytes. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
open Caliper BoundedSource
variable {w qH qS randomBound : Nat} {M F G : Type} (layout : Layouts w M F G qH qS randomBound)

def markValue (args : Nat × Signatures.Runtime.SchnorrAGM.Native.EncodedState F G M) :=
  (args.1, Signatures.Runtime.SchnorrAGM.Native.Random.marked false args.2)
theorem mark_valid (args : Nat × Signatures.Runtime.SchnorrAGM.Native.EncodedState F G M)
    (valid : layout.base.valid args) : layout.base.valid (markValue args) :=
  ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1, trivial, valid.2.2.2.2.2⟩
def markResult (args : layout.base.Value) : layout.base.Value := ⟨markValue args.val, mark_valid layout args.val args.property⟩
def markOffset : Nat := 1 + layout.scheme.cache.lookup.table.representation.encoding.words +
  layout.scheme.basis.representation.encoding.words + layout.scheme.signed.representation.encoding.words
def leadingBytes (args : layout.base.Value) : List (Word w) :=
  layout.counter.representation.encoding.encode ⟨args.val.1, args.property.1⟩ ++
    layout.scheme.cache.lookup.table.representation.encoding.encode ⟨args.val.2.1, args.property.2.1⟩ ++
      layout.scheme.basis.representation.encoding.encode ⟨args.val.2.2.1, args.property.2.2.1⟩ ++
        layout.scheme.signed.representation.encoding.encode ⟨args.val.2.2.2.1, args.property.2.2.2.1⟩
theorem leadingBytes_length (args : layout.base.Value) : (leadingBytes layout args).length = markOffset layout := by
  simp only [leadingBytes, List.length_append, Encoding.encode_length]
  rfl
theorem base_bytes (args : layout.base.Value) : layout.base.representation.encoding.encode args =
    leadingBytes layout args ++ [if args.val.2.2.2.2.1 then 1 else 0, if args.val.2.2.2.2.2 then 1 else 0] := by
  change _ ++ (_ ++ (_ ++ (_ ++ ([if args.val.2.2.2.2.1 then 1 else 0] ++ [if args.val.2.2.2.2.2 then 1 else 0])))) = _
  simp only [leadingBytes, List.append_assoc]
  rfl
theorem base_words : layout.base.representation.encoding.words = markOffset layout + 2 := by
  change 1 + (_ + (_ + (_ + (1 + 1)))) = (1 + _ + _ + _) + 2
  omega
theorem markOffset_fits : markOffset layout < 2 ^ w := by
  have fits := layout.base.representation.fits
  rw [base_words] at fits
  omega
theorem marked_bytes (args : layout.base.Value) : layout.base.representation.encoding.encode (markResult layout args) =
    leadingBytes layout args ++ [1, if args.val.2.2.2.2.2 then 1 else 0] := by
  rw [base_bytes]
  rfl

def mark : Implementation .unit layout.base layout.base markValue where
  preserves := mark_valid layout
  program := {
    code := CellArithmetic.code (markOffset layout) .or 1
    positive_width := width_pos layout.scheme.wordFits
    description_fits := CellArithmetic.descriptionFits _ _ _ layout.scheme.wordFits
    random_free := CellArithmetic.randomFree _ _ _
    time _ := 5
    net _ := 0
    workspace _ := 0
    correct := by
      intro tape args before represented
      have contents := represented.2.1
      rw [base_bytes] at contents
      obtain ⟨after, execution, result, zero, caps⟩ := CellArithmetic.exec_at .unit tape (leadingBytes layout args)
        [if args.val.2.2.2.2.2 then 1 else 0] (if args.val.2.2.2.2.1 then 1 else 0) 1 .or before contents
        (by rw [leadingBytes_length]; exact markOffset_fits layout)
      rw [leadingBytes_length] at execution
      refine ⟨after, 0, 0, execution, ⟨zero.trans represented.1, ?_,
        execution.wellFormed_preserved represented.2.2.1, ?_⟩, le_rfl, le_rfl⟩
      · change (after.bufs 0).toList = layout.base.representation.encoding.encode (markResult layout args)
        rw [marked_bytes]
        cases flag : args.val.2.2.2.2.1 <;> simpa [flag, BinOp.eval] using result
      · intro buffer
        rw [caps]
        exact represented.2.2.2 buffer }
theorem mark_bounded : (mark layout).BoundedBy 5 23 := ⟨fun _ => le_rfl, le_rfl⟩
theorem mark_names (slots : Nat) : NamesAccounted (mark layout).program.code slots := CellArithmetic.names _ _ _ slots
theorem mark_buffers : (mark layout).program.code.memBound ≤ 1 := CellArithmetic.buffers _ _ _

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
