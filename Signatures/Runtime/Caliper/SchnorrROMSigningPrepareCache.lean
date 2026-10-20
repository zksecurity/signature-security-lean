import Signatures.Runtime.Caliper.SchnorrROMSigningArguments

/-! Copy the computed commitment, challenge and managed table into the cache
programmer's input, retaining the signature and public configuration. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Arithmetic
open Caliper BoundedSource ByteRoute
variable {w : Nat} {M F G : Type} [DecidableEq M] [DecidableEq G] (layout : Layouts w M F G)

def message (value : layout.input.Value) : layout.message.Value :=
  ⟨value.val.2.2.2.1, value.property.1.2.2.2.1⟩
def table (value : layout.input.Value) : layout.table.Value :=
  ⟨value.val.2.2.2.2, value.property.1.2.2.2.2⟩

def finishValue (value : layout.point.Value × layout.input.Value) : layout.work.Value :=
  ⟨(((value.2.val.2.2.2.1, value.1.val), value.2.val.1.1, value.2.val.2.2.2.2, ()),
    (value.1.val, value.2.val.1.2), value.2.val.2.1, value.2.val.2.2.1),
    ⟨⟨⟨(message layout value.2).property, value.1.property⟩, (challenge layout value.2).property,
      (table layout value.2).property, trivial⟩, fun _ => value.2.property.2⟩,
    ⟨value.1.property, (response layout value.2).property⟩,
    (generator layout value.2).property, (publicKey layout value.2).property⟩

def finishParts : List (Part w) :=
  [.slice (3 * layout.point.representation.encoding.words + 2 * layout.scalar.representation.encoding.words)
      layout.message.representation.encoding.words,
   .slice 0 layout.point.representation.encoding.words,
   .slice layout.point.representation.encoding.words layout.scalar.representation.encoding.words,
   .slice (3 * layout.point.representation.encoding.words + 2 * layout.scalar.representation.encoding.words +
      layout.message.representation.encoding.words) layout.table.representation.encoding.words,
   .slice 0 layout.point.representation.encoding.words,
   .slice (layout.point.representation.encoding.words + layout.scalar.representation.encoding.words)
      layout.scalar.representation.encoding.words,
   .slice (layout.point.representation.encoding.words + 2 * layout.scalar.representation.encoding.words)
      (2 * layout.point.representation.encoding.words)]

omit [DecidableEq M] [DecidableEq G] in
theorem finish_valid : Valid layout.frame.encoding.words (finishParts layout) := by
  change Valid (layout.point.representation.encoding.words + layout.input.representation.encoding.words) _
  rw [Layouts.input_words]
  simp only [finishParts, Valid]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, trivial⟩

theorem finish_size : words (finishParts layout) = layout.work.representation.encoding.words := by
  simp only [finishParts, words]
  change _ = layout.cache.lookup.input.representation.encoding.words +
    ((layout.point.representation.encoding.words + layout.scalar.representation.encoding.words) +
      (layout.point.representation.encoding.words + layout.point.representation.encoding.words))
  rw [LookupLayout.input_words]
  change _ = (1 + (layout.capacityPred + 1) * (layout.message.representation.encoding.words + layout.point.representation.encoding.words +
    layout.scalar.representation.encoding.words) + (layout.message.representation.encoding.words + layout.point.representation.encoding.words) +
    layout.scalar.representation.encoding.words) + _
  rw [Layouts.table_words]
  omega

theorem finish_bytes (value : layout.point.Value × layout.input.Value) :
    bytes (layout.frame.encoding.encode value) (finishParts layout) =
      layout.work.representation.encoding.encode (finishValue layout value) := by
  let p := layout.point.representation.encoding.encode value.1
  let c := layout.scalar.representation.encoding.encode (challenge layout value.2)
  let s := layout.scalar.representation.encoding.encode (response layout value.2)
  let g := layout.point.representation.encoding.encode (generator layout value.2)
  let pk := layout.point.representation.encoding.encode (publicKey layout value.2)
  let msg := layout.message.representation.encoding.encode (message layout value.2)
  let cache := layout.table.representation.encoding.encode (table layout value.2)
  have hp : p.length = layout.point.representation.encoding.words := Encoding.encode_length _ _
  have hc : c.length = layout.scalar.representation.encoding.words := Encoding.encode_length _ _
  have hs : s.length = layout.scalar.representation.encoding.words := Encoding.encode_length _ _
  have hg : g.length = layout.point.representation.encoding.words := Encoding.encode_length _ _
  have hpk : pk.length = layout.point.representation.encoding.words := Encoding.encode_length _ _
  have hm : msg.length = layout.message.representation.encoding.words := Encoding.encode_length _ _
  have ht : cache.length = layout.table.representation.encoding.words := Encoding.encode_length _ _
  have point := slice_block [] p (c ++ s ++ g ++ pk ++ msg ++ cache)
  have challenge := slice_block p c (s ++ g ++ pk ++ msg ++ cache)
  have response := slice_block (p ++ c) s (g ++ pk ++ msg ++ cache)
  have config := slice_block (p ++ c ++ s) (g ++ pk) (msg ++ cache)
  have message := slice_block (p ++ c ++ s ++ g ++ pk) msg cache
  have table := slice_block (p ++ c ++ s ++ g ++ pk ++ msg) cache []
  simp only [List.length_nil, List.nil_append, List.length_append, List.append_nil, hp, hc, hs, hg, hpk, hm, ht,
    List.append_assoc] at point challenge response config message table
  simp only [← Nat.add_assoc] at response config message table
  have messageOffset : layout.point.representation.encoding.words + layout.scalar.representation.encoding.words +
      layout.scalar.representation.encoding.words + layout.point.representation.encoding.words +
      layout.point.representation.encoding.words = 3 * layout.point.representation.encoding.words + 2 * layout.scalar.representation.encoding.words := by omega
  have configOffset : layout.point.representation.encoding.words + layout.scalar.representation.encoding.words +
      layout.scalar.representation.encoding.words = layout.point.representation.encoding.words + 2 * layout.scalar.representation.encoding.words := by omega
  have configSize : layout.point.representation.encoding.words + layout.point.representation.encoding.words =
      2 * layout.point.representation.encoding.words := by omega
  rw [messageOffset] at message table
  rw [configOffset, configSize] at config
  change bytes (p ++ ((c ++ s) ++ (g ++ (pk ++ (msg ++ cache))))) (finishParts layout) =
    ((msg ++ p) ++ (c ++ (cache ++ []))) ++ ((p ++ s) ++ (g ++ pk))
  simp only [finishParts, bytes, List.append_nil, List.append_assoc]
  rw [point, challenge, response, config, message, table]

def finish : Realizer .unit layout.frame layout.work.representation (finishValue layout) :=
  ByteRoute.realizer _ _ _ (finishParts layout) layout.wordFits (finish_valid layout) (finish_size layout) (finish_bytes layout)
theorem finish_time (value) : (finish layout).time value ≤ 8 * layout.work.representation.encoding.words :=
  ByteRoute.time _ _ _ _ _ _ _ _ value
theorem finish_words : descriptionWords (finish layout).code ≤ 26 * layout.work.representation.encoding.words + 14 :=
  ByteRoute.codeWords _ _ _ _ _ _ _ _
theorem finish_buffers : (finish layout).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
theorem finish_names (slots : Nat) : NamesAccounted (finish layout).code slots := ByteRoute.names _ _ _ _ _ _ _ _ slots

end Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Arithmetic
