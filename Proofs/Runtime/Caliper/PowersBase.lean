import Proofs.Runtime.Caliper.VectorLayout
import Proofs.Runtime.Caliper.EncodedConstant
import Proofs.Runtime.Caliper.ImplementationMemory

/-! Successive scalar powers use an implemented multiplication routine and
paid copies of the running scalar pair. Dimension-dependent code is accounted
for separately from the multiplication primitive's own code and time. -/
namespace Signatures.Runtime.CaliperBackend.Powers
open Caliper BoundedSource

structure Layouts (w : Nat) (F : Type) (capacity : Nat) where
  scalar : Layout w F
  wordFits : 16 < 2 ^ w
  storageFits : 64 * ((capacity + 2) * (1 + scalar.representation.encoding.words)) < 2 ^ w

namespace Layouts
variable {w capacity : Nat} {F : Type} (layout : Layouts w F capacity)
def width : Nat := (capacity + 2) * (1 + layout.scalar.representation.encoding.words)
theorem fits_of_le {words : Nat} (bound : words ≤ 64 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits
def input := layout.scalar.prod layout.scalar
  (layout.fits_of_le (by unfold width; nlinarith))
def vector (n : Nat) (bound : n ≤ capacity) := layout.scalar.vector n
  (layout.fits_of_le (by unfold width; nlinarith))
theorem scalar_le : layout.scalar.representation.encoding.words ≤ layout.width := by unfold width; nlinarith
theorem input_le : layout.input.representation.encoding.words ≤ layout.width := by
  change layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words ≤ _
  unfold width
  nlinarith
theorem vector_le (n : Nat) (bound : n ≤ capacity) :
    (layout.vector n bound).representation.encoding.words ≤ layout.width := by
  change (vectorEncoding layout.scalar n).words ≤ _
  rw [vectorEncoding_words]
  unfold width
  nlinarith
end Layouts

variable {w capacity : Nat} {F : Type} [Mul F] (layout : Layouts w F capacity)

def next (input : F × F) : F × F := (input.1, input.1 * input.2)
def values : (n : Nat) → (F × F) → Fin n → F
  | 0, _ => Fin.elim0
  | n + 1, input => Fin.cases input.2 (values n (next input))

def baseSlots (slots : Nat) : Nat := max 4 slots + 2

variable (mul : Implementation .unit layout.input layout.scalar (fun input => input.1 * input.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots)
    (reserve : baseSlots slots + capacity < 2 ^ w)

include reserve in
theorem nameFits {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (body : Implementation .unit input output f)
    (bound : body.program.code.memBound ≤ baseSlots slots + capacity) :
    body.program.savedBuffer < 2 ^ w := by
  change max 2 body.program.code.memBound < _
  have lower : 2 ≤ baseSlots slots := by unfold baseSlots; omega
  omega

def base : Implementation .unit layout.input layout.scalar Prod.fst :=
  Implementation.first (by decide) layout.scalar layout.scalar layout.wordFits _
def current : Implementation .unit layout.input layout.scalar Prod.snd :=
  Implementation.second (by decide) layout.scalar layout.scalar layout.wordFits _
omit [Mul F] in
theorem base_buffers : (base layout).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
omit [Mul F] in
theorem current_buffers : (current layout).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _

def step : Implementation .unit layout.input layout.input next :=
  (base layout).pair mul (by decide) layout.wordFits
    (nameFits reserve _ ((base_buffers layout).trans (by unfold baseSlots; omega)))
    (nameFits reserve _ (mulBuffers.trans (by unfold baseSlots; omega)))
    (layout.fits_of_le (by have := layout.input_le; omega))
    (layout.fits_of_le (by have := layout.input_le; have := layout.scalar_le; omega))
    layout.input.representation.fits

theorem step_buffers : (step layout mul mulBuffers reserve).program.code.memBound ≤ baseSlots slots := by
  have bounded := Implementation.pair_buffers (base layout) mul layout.wordFits
    (nameFits reserve _ ((base_buffers layout).trans (by unfold baseSlots; omega)))
    (nameFits reserve _ (mulBuffers.trans (by unfold baseSlots; omega)))
    (layout.fits_of_le (by have := layout.input_le; omega))
    (layout.fits_of_le (by have := layout.input_le; have := layout.scalar_le; omega))
    layout.input.representation.fits (base_buffers layout) mulBuffers
  exact bounded.trans (by unfold baseSlots; omega)

theorem step_bounded {mulTime mulWords : Nat} (bound : mul.BoundedBy mulTime mulWords) :
    (step layout mul mulBuffers reserve).BoundedBy
      (mulTime + 200 * layout.width) (mulWords + 600 * layout.width + 200) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _
    (Implementation.first_boundedBy _ _ _ _) bound).mono
  all_goals
    have inputBound := layout.input_le
    have scalarBound := layout.scalar_le
    dsimp only [Layouts.input, Layout.prod, Representation.transport, Representation.prod,
      Encoding.transport, Encoding.prod, Encoding.checked] at inputBound ⊢
    omega

theorem step_names {names : Nat} (named : NamesAccounted mul.program.code names) :
    NamesAccounted (step layout mul mulBuffers reserve).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (Implementation.first_names _ _ _ _ _) named

end Signatures.Runtime.CaliperBackend.Powers
