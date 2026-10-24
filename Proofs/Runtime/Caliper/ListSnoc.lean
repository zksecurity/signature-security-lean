import Proofs.Runtime.Caliper.ListReverseBounds
import Proofs.Runtime.Caliper.ListNarrow

/-! Chronological append within a bounded source list. Both reversals, the
temporary extra slot and the final padding removal are executed and charged.
The free-slot predicate also gives the correct empty domain at capacity zero. -/
namespace Signatures.Runtime.CaliperBackend.ListSnoc
open Caliper BoundedSource

structure Layouts (w : Nat) (A : Type) where
  entry : Layout w A
  capacity : Nat
  wordFits : 16 < 2 ^ w
  countFits : capacity + 1 < 2 ^ w
  storageFits : 16 * (1 + (capacity + 2) * entry.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {A : Type} (layout : Layouts w A)
def width : Nat := 1 + (layout.capacity + 2) * layout.entry.representation.encoding.words
theorem fits_of_le {words : Nat} (bound : words ≤ 16 * layout.width) : words < 2 ^ w := bound.trans_lt layout.storageFits
def reversal : ListReverse.Layouts w A where
  entry := layout.entry
  capacity := layout.capacity
  wordFits := layout.wordFits
  countFits := by have := layout.countFits; omega
  storageFits := layout.fits_of_le (by unfold width; nlinarith)
def extended : ListReverse.Layouts w A where
  entry := layout.entry
  capacity := layout.capacity + 1
  wordFits := layout.wordFits
  countFits := layout.countFits
  storageFits := layout.fits_of_le (by unfold width; nlinarith)
def list := layout.reversal.list
def grown := layout.extended.list
def raw : Layout w (A × List A) := layout.entry.prod layout.list
  (layout.fits_of_le (by
    change layout.entry.representation.encoding.words + (1 + layout.capacity * layout.entry.representation.encoding.words) ≤ _
    unfold width; nlinarith))
def input : Layout w (A × List A) := layout.raw.restrict (fun input => input.2.length < layout.capacity)
theorem sizes : layout.entry.representation.encoding.words ≤ layout.width ∧ layout.list.representation.encoding.words ≤ layout.width ∧
    layout.grown.representation.encoding.words ≤ layout.width ∧ layout.raw.representation.encoding.words ≤ layout.width := by
  change _ ≤ _ ∧ 1 + layout.capacity * layout.entry.representation.encoding.words ≤ _ ∧
    1 + (layout.capacity + 1) * layout.entry.representation.encoding.words ≤ _ ∧
      layout.entry.representation.encoding.words + (1 + layout.capacity * layout.entry.representation.encoding.words) ≤ _
  refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold width <;> nlinarith
end Layouts

variable {w : Nat} {A : Type} (layout : Layouts w A)

def entry : Implementation .unit layout.raw layout.entry Prod.fst :=
  Implementation.first (by decide) layout.entry layout.list layout.wordFits _
def reversed : Implementation .unit layout.raw layout.list (fun input => input.2.reverse) :=
  (Implementation.second (by decide) layout.entry layout.list layout.wordFits _).then
    (ListReverse.implementation layout.reversal)
theorem entry_buffers : (entry layout).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
theorem reversed_buffers : (reversed layout).program.code.memBound ≤ 3 :=
  max_le ((Implementation.second_buffers _ _ _ _ _).trans (by decide)) (ListReverse.buffers layout.reversal)
include layout in
theorem nameFits {X Y : Type} {input : Layout w X} {output : Layout w Y} {f : X → Y}
    (body : Implementation .unit input output f) (bound : body.program.code.memBound ≤ 3) : body.program.savedBuffer < 2 ^ w := by
  have := layout.wordFits
  change max 2 body.program.code.memBound < 2 ^ w
  omega
def prepare : Implementation .unit layout.raw layout.raw (fun input => (input.1, input.2.reverse)) :=
  (entry layout).pair (reversed layout) (by decide) layout.wordFits
    (nameFits layout _ ((entry_buffers layout).trans (by decide))) (nameFits layout _ (reversed_buffers layout))
    (layout.fits_of_le (by have := layout.sizes; omega))
    (layout.fits_of_le (by have := layout.sizes; omega)) layout.raw.representation.fits
def prepend : Implementation .unit layout.raw layout.grown (fun input => input.1 :: input.2) :=
  ListData.cons .unit (by decide) layout.entry layout.capacity layout.wordFits layout.countFits layout.grown.representation.fits
def appended : Implementation .unit layout.raw layout.grown (fun input => input.2 ++ [input.1]) :=
  (((prepare layout).then (prepend layout)).then (ListReverse.implementation layout.extended)).castFunction (by
    funext input
    simp only [Function.comp_apply, List.reverse_cons, List.reverse_reverse])
def admitted : Implementation .unit layout.input
    (layout.grown.restrict (fun values => values.length ≤ layout.capacity)) (fun input => input.2 ++ [input.1]) :=
  ((appended layout).restrictInput (fun input => input.2.length < layout.capacity)).restrictOutput
    (fun values => values.length ≤ layout.capacity) (by
      intro input valid
      simp only [List.length_append, List.length_singleton]
      exact Nat.succ_le_of_lt valid.2)
def implementation : Implementation .unit layout.input layout.list (fun input => input.2 ++ [input.1]) :=
  (admitted layout).then (ListData.narrow .unit (by decide) layout.entry (layout.capacity + 1) layout.capacity (by omega)
    layout.wordFits layout.countFits layout.grown.representation.fits)

theorem buffers : (implementation layout).program.code.memBound ≤ 4 := by
  have paired := Implementation.pair_buffers (entry layout) (reversed layout) layout.wordFits
    (nameFits layout _ ((entry_buffers layout).trans (by decide))) (nameFits layout _ (reversed_buffers layout))
    (layout.fits_of_le (by have := layout.sizes; omega))
    (layout.fits_of_le (by have := layout.sizes; omega)) layout.raw.representation.fits
    (entry_buffers layout) (reversed_buffers layout)
  have constructed := (Assembly.code_names (ListConstruct.consOperands (w := w) layout.entry.representation.encoding.words layout.capacity) 1 (by
    simp only [ListConstruct.consOperands, Assembly.sourcesBound_append]
    exact ⟨⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩,
      Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩)).2
  have increment := CellArithmetic.buffers (w := w) 0 .add 1
  have prepended : (prepend layout).program.code.memBound ≤ 2 := max_le constructed (increment.trans (by decide))
  have reversed := ListReverse.buffers layout.extended
  have narrowed := ListData.narrow_buffers .unit (by decide) layout.entry (layout.capacity + 1) layout.capacity (by omega)
    layout.wordFits layout.countFits layout.grown.representation.fits
  change max (max (max (prepare layout).program.code.memBound (prepend layout).program.code.memBound)
    (ListReverse.implementation layout.extended).program.code.memBound) _ ≤ _
  exact max_le (max_le (max_le paired (prepended.trans (by decide))) (reversed.trans (by decide))) (narrowed.trans (by decide))

theorem names (slots : Nat) : NamesAccounted (implementation layout).program.code slots :=
  (((Implementation.pair_names _ _ _ _ _ _ _ _ (Implementation.first_names _ _ _ _ _)
    ((Implementation.second_names _ _ _ _ _).seq (ListReverse.names layout.reversal slots))).seq
      (ListData.cons_names layout.entry layout.capacity layout.wordFits layout.countFits layout.grown.representation.fits slots)).seq
        (ListReverse.names layout.extended slots)).seq (selectSlice_names _ _ slots)

end Signatures.Runtime.CaliperBackend.ListSnoc
