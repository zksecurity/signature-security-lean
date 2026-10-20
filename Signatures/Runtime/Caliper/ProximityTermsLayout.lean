import Signatures.Runtime.Caliper.VectorLayout
import Signatures.Runtime.Caliper.Finite
import Signatures.Runtime.Caliper.ImplementationMemory
import Signatures.Runtime.ProximityWeight

/-! Bounded layouts for Proximity's original vector/slot messages and their
dimension-plus-one weighted terms. Scalar domains are never enumerated. -/
namespace Signatures.Runtime.CaliperBackend.ProximityTerms
open Caliper BoundedSource

structure Layouts (w : Nat) (F K : Type) (dimension : Nat) where
  scalar : Layout w F
  label : Layout w K
  wordFits : 16 < 2 ^ w
  countFits : dimension + 1 < 2 ^ w
  storageFits : 4 * (1 + (dimension + 1) *
    (1 + label.representation.encoding.words + scalar.representation.encoding.words)) < 2 ^ w

namespace Layouts
variable {w dimension : Nat} {F K : Type} (layout : Layouts w F K dimension)

def width : Nat := 1 + (dimension + 1) *
  (1 + layout.label.representation.encoding.words + layout.scalar.representation.encoding.words)
theorem fits_of_le {words : Nat} (bound : words ≤ 4 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits
def vector := layout.scalar.vector dimension (layout.fits_of_le (by unfold width; nlinarith))
def input : Layout w ((Fin dimension → F) × K) := layout.vector.prod layout.label
  (layout.fits_of_le (by
    change (vectorEncoding layout.scalar dimension).words + _ ≤ _
    rw [vectorEncoding_words]
    unfold width
    nlinarith))
def index : Layout w (Fin (dimension + 1)) :=
  Finite.layout dimension layout.wordFits (Nat.le_of_lt layout.countFits)
def key : Layout w (Fin (dimension + 1) × K) := layout.index.prod layout.label
  (layout.fits_of_le (by change 1 + _ ≤ _; unfold width; nlinarith))
def term : Layout w ((Fin (dimension + 1) × K) × F) := layout.key.prod layout.scalar
  (layout.fits_of_le (by change (1 + _) + _ ≤ _; unfold width; nlinarith))
def output := layout.term.boundedList (dimension + 1) layout.countFits
  (layout.fits_of_le (by change 1 + (dimension + 1) * ((1 + _) + _) ≤ _; unfold width; omega))

theorem vector_words : layout.vector.representation.encoding.words =
    dimension * layout.scalar.representation.encoding.words := vectorEncoding_words _ _
theorem input_words : layout.input.representation.encoding.words =
    dimension * layout.scalar.representation.encoding.words + layout.label.representation.encoding.words := by
  change layout.vector.representation.encoding.words + _ = _
  rw [vector_words]
theorem term_words : layout.term.representation.encoding.words =
    1 + layout.label.representation.encoding.words + layout.scalar.representation.encoding.words := rfl
theorem output_words : layout.output.representation.encoding.words = layout.width := rfl
end Layouts

variable {dimension : Nat} {F K : Type} [One F]

def value (input : (Fin dimension → F) × K) : List ((Fin (dimension + 1) × K) × F) :=
  List.ofFn (fun i => ((i, input.2), Fin.cases 1 input.1 i))

theorem source (input : (Fin dimension → F) × K) :
    value input = (Proximity.LazyAGM.terms input).map (Prod.map Weights.encodeProximityKey id) := by
  simp only [value, Proximity.LazyAGM.terms, List.ofFn_succ, List.map_cons, List.map_ofFn,
    Function.comp_def, Prod.map, Weights.encodeProximityKey, Fin.cases_zero, Fin.cases_succ, id_eq]
  rfl

variable {w : Nat} (layout : Layouts w F K dimension) (oneValid : layout.scalar.valid (1 : F))

include oneValid in
theorem preserves (input : (Fin dimension → F) × K) (valid : layout.input.valid input) :
    layout.output.valid (value input) := by
  refine ⟨by simp [value], ?_⟩
  intro term member
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
  exact ⟨⟨trivial, valid.2⟩, Fin.cases oneValid valid.1 i⟩

end Signatures.Runtime.CaliperBackend.ProximityTerms
