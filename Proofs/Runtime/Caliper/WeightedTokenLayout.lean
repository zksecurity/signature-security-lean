import Proofs.Runtime.Caliper.WeightedCoefficientBounds

/-! A signing transcript row carries a message, its delivered point and its
positional coefficient. Extraction copies the message/coefficient and current
state into the weighted evaluator; the delivered point is no longer needed. -/
namespace Signatures.Runtime.CaliperBackend.WeightedToken
open Caliper BoundedSource ByteRoute

structure Layouts (w : Nat) (K M G F R : Type) where
  weighted : WeightedCoefficient.Layouts w K M F R
  point : Layout w G
  storageFits : 16 * (weighted.width + point.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {K M G F R : Type} (layout : Layouts w K M G F R)
abbrev accumulation := layout.weighted.evaluation
abbrev state := layout.weighted.state
def width := layout.weighted.width + layout.point.representation.encoding.words
theorem fits {words : Nat} (bound : words ≤ 16 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits
def token := layout.weighted.message.prod layout.point (layout.fits (by
  unfold width WeightedCoefficient.Layouts.width
  omega))
def row := layout.token.prod layout.accumulation.coefficient (layout.fits (by
  change (_ + _) + _ ≤ _
  have := layout.accumulation.base_sizes
  unfold width WeightedCoefficient.Layouts.width
  dsimp only [accumulation] at *
  omega))
def input := layout.row.representation.prod layout.state.representation (layout.fits (by
  change ((_ + _) + _) + (_ + _) ≤ _
  dsimp only [WeightedRows.rows]
  have := layout.accumulation.base_sizes
  unfold width WeightedCoefficient.Layouts.width
  dsimp only [accumulation] at *
  omega))
theorem state_words : layout.state.representation.encoding.words =
    layout.accumulation.cache.value.representation.encoding.words +
      layout.accumulation.cache.lookup.table.representation.encoding.words := rfl
include layout in
theorem nameFits {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (body : Implementation .unit input output f) {buffers : Nat}
    (bound : body.program.code.memBound ≤ buffers) (small : buffers ≤ 16) :
    body.program.savedBuffer < 2 ^ w :=
  CacheAccumulate.nameFits layout.accumulation body bound (small.trans_lt layout.accumulation.cache.wordFits)
end Layouts

variable {w : Nat} {K M G F R : Type} (layout : Layouts w K M G F R)
abbrev Input := layout.row.Value × layout.state.Value
def argument (value : Input layout) : layout.weighted.input.Value :=
  ⟨(value.1.val.1.1, value.1.val.2, value.2.val),
    value.1.property.1.1, value.1.property.2, value.2.property⟩
def parts : List (Part w) :=
  [.slice 0 layout.weighted.message.representation.encoding.words,
   .slice (layout.weighted.message.representation.encoding.words + layout.point.representation.encoding.words)
     (layout.accumulation.coefficient.representation.encoding.words + layout.state.representation.encoding.words)]
theorem parts_valid : ByteRoute.Valid layout.input.encoding.words (parts layout) := by
  change (0 + _ ≤ ((_ + _) + _) + _) ∧ ((_ + _) + (_ + _) ≤ ((_ + _) + _) + _) ∧ True
  exact ⟨by omega, by omega, trivial⟩
theorem parts_words : ByteRoute.words (parts layout) = layout.weighted.input.representation.encoding.words := by
  change _ + ((_ + _) + 0) = _ + (_ + _)
  dsimp only [Layouts.accumulation, Layouts.state]
  omega
theorem argument_bytes (value : Input layout) :
    ByteRoute.bytes (layout.input.encoding.encode value) (parts layout) =
      layout.weighted.input.representation.encoding.encode (argument layout value) := by
  let m := layout.weighted.message.representation.encoding.encode
    ⟨value.1.val.1.1, value.1.property.1.1⟩
  let g := layout.point.representation.encoding.encode ⟨value.1.val.1.2, value.1.property.1.2⟩
  let c := layout.accumulation.coefficient.representation.encoding.encode ⟨value.1.val.2, value.1.property.2⟩
  let s := layout.state.representation.encoding.encode value.2
  have hm : m.length = layout.weighted.message.representation.encoding.words := Encoding.encode_length _ _
  have hg : g.length = layout.point.representation.encoding.words := Encoding.encode_length _ _
  have hc : c.length = layout.accumulation.coefficient.representation.encoding.words := Encoding.encode_length _ _
  have hs : s.length = layout.state.representation.encoding.words := Encoding.encode_length _ _
  have messageRead := ByteRoute.slice_block [] m (g ++ c ++ s)
  have restRead := ByteRoute.slice_block (m ++ g) (c ++ s) []
  simp only [List.nil_append, List.append_nil, List.length_nil, List.length_append,
    hm, hg, hc, hs, List.append_assoc] at messageRead restRead
  change ((((m ++ g) ++ c) ++ s).drop 0).take _ ++
    (((((m ++ g) ++ c) ++ s).drop (_ + _)).take (_ + _) ++ []) = _
  simp only [List.append_assoc]
  rw [messageRead, restRead]
  change _ = m ++ (c ++ s)
  simp only [List.append_nil]
def prepare : Realizer .unit layout.input layout.weighted.input.representation (argument layout) :=
  ByteRoute.realizer _ _ _ (parts layout) layout.accumulation.cache.wordFits
    (parts_valid layout) (parts_words layout) (argument_bytes layout)

def room (terms remaining : Nat) (value : layout.state.Value) : Prop :=
  value.val.2.length + terms * remaining ≤ layout.accumulation.cache.capacityPred + 1

end Signatures.Runtime.CaliperBackend.WeightedToken
