import Signatures.Runtime.Caliper.FiniteZero
import Signatures.Runtime.Caliper.PairBounds

/-! Stored scalar/coin and challenge-point arguments for Coron replies.
One storage-width condition covers the generated projection and pairing frames. -/
namespace Signatures.Runtime.CaliperBackend.CoronResponse
open Caliper BoundedSource

structure Layouts (w : Nat) (F G : Type) (qS : Nat) where
  scalar : Layout w F
  point : Layout w G
  wordFits : 16 < 2 ^ w
  coinFits : qS + 1 ≤ 2 ^ w
  storageFits : 16 * (scalar.representation.encoding.words + point.representation.encoding.words + 1) < 2 ^ w

namespace Layouts
variable {w qS : Nat} {F G : Type} (layout : Layouts w F G qS)

theorem fits_of_le {words : Nat}
    (bound : words ≤ 16 * (layout.scalar.representation.encoding.words + layout.point.representation.encoding.words + 1)) :
    words < 2 ^ w := bound.trans_lt layout.storageFits

def coin : Layout w (Fin (qS + 1)) := Finite.layout qS layout.wordFits layout.coinFits
def entry : Layout w (F × Fin (qS + 1)) := layout.scalar.prod layout.coin (layout.fits_of_le (by change _ + 1 ≤ _; omega))
def points : Layout w (G × G) := layout.point.prod layout.point (layout.fits_of_le (by omega))
def config : Layout w (G × (G × G)) := layout.point.prod layout.points (layout.fits_of_le (by change _ + (_ + _) ≤ _; omega))
def input : Layout w ((F × Fin (qS + 1)) × (G × (G × G))) := layout.entry.prod layout.config
  (layout.fits_of_le (by change (_ + 1) + (_ + (_ + _)) ≤ _; omega))
def scaleArgs : Layout w (F × G) := layout.scalar.prod layout.point (layout.fits_of_le (by omega))
def width : Nat := layout.scalar.representation.encoding.words + 1 + 3 * layout.point.representation.encoding.words

@[simp] theorem entry_words : layout.entry.representation.encoding.words = layout.scalar.representation.encoding.words + 1 := rfl
@[simp] theorem points_words : layout.points.representation.encoding.words = 2 * layout.point.representation.encoding.words := by change _ + _ = _; omega
@[simp] theorem config_words : layout.config.representation.encoding.words = 3 * layout.point.representation.encoding.words := by change _ + (_ + _) = _; omega
@[simp] theorem input_words : layout.input.representation.encoding.words = layout.width := by change (_ + 1) + (_ + (_ + _)) = _; unfold width; omega

theorem duplicateFits : layout.input.representation.encoding.words + layout.input.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by rw [input_words]; unfold width; omega)
theorem tagFits : 1 + layout.input.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by rw [input_words]; unfold width; omega)

end Layouts

variable {w qS : Nat} {F G : Type} (layout : Layouts w F G qS)

def scalarValue : Implementation .unit layout.input layout.scalar (fun value => value.1.1) :=
  (Implementation.first (by decide) layout.entry layout.config layout.wordFits _).then
    (Implementation.first (by decide) layout.scalar layout.coin layout.wordFits _)
def coinValue : Implementation .unit layout.input layout.coin (fun value => value.1.2) :=
  (Implementation.first (by decide) layout.entry layout.config layout.wordFits _).then
    (Implementation.second (by decide) layout.scalar layout.coin layout.wordFits _)
def configuration : Implementation .unit layout.input layout.config Prod.snd :=
  Implementation.second (by decide) layout.entry layout.config layout.wordFits _
def tailPoints : Implementation .unit layout.input layout.points (fun value => value.2.2) :=
  (configuration layout).then (Implementation.second (by decide) layout.point layout.points layout.wordFits _)
def basePoint : Implementation .unit layout.input layout.point (fun value => value.2.1) :=
  (configuration layout).then (Implementation.first (by decide) layout.point layout.points layout.wordFits _)
def keyPoint : Implementation .unit layout.input layout.point (fun value => value.2.2.1) :=
  (tailPoints layout).then (Implementation.first (by decide) layout.point layout.point layout.wordFits _)
def challengePoint : Implementation .unit layout.input layout.point (fun value => value.2.2.2) :=
  (tailPoints layout).then (Implementation.second (by decide) layout.point layout.point layout.wordFits _)
def selectedPoint (signing : Bool) : Implementation .unit layout.input layout.point
    (fun value => if signing then value.2.2.1 else value.2.1) := by
  cases signing
  · exact basePoint layout
  · exact keyPoint layout

def condition (value : (F × Fin (qS + 1)) × (G × (G × G))) : Bool := decide (value.1.2 = 0)
def test : Implementation .unit layout.input (DataImplementation.boolLayout w (width_pos layout.wordFits)) condition :=
  (coinValue layout).then (Finite.isZero qS layout.wordFits layout.coinFits)

theorem scalarValue_buffers : (scalarValue layout).program.code.memBound ≤ 2 :=
  max_le (Implementation.first_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)
theorem coinValue_buffers : (coinValue layout).program.code.memBound ≤ 2 :=
  max_le (Implementation.first_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _)
theorem configuration_buffers : (configuration layout).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _
theorem tailPoints_buffers : (tailPoints layout).program.code.memBound ≤ 2 :=
  max_le (configuration_buffers layout) (Implementation.second_buffers _ _ _ _ _)
theorem basePoint_buffers : (basePoint layout).program.code.memBound ≤ 2 :=
  max_le (configuration_buffers layout) (Implementation.first_buffers _ _ _ _ _)
theorem keyPoint_buffers : (keyPoint layout).program.code.memBound ≤ 2 :=
  max_le (tailPoints_buffers layout) (Implementation.first_buffers _ _ _ _ _)
theorem challengePoint_buffers : (challengePoint layout).program.code.memBound ≤ 2 :=
  max_le (tailPoints_buffers layout) (Implementation.second_buffers _ _ _ _ _)
theorem selectedPoint_buffers (signing : Bool) : (selectedPoint layout signing).program.code.memBound ≤ 2 := by
  cases signing
  · exact basePoint_buffers layout
  · exact keyPoint_buffers layout
theorem test_buffers : (test layout).program.code.memBound ≤ 2 :=
  max_le (coinValue_buffers layout) ((Finite.isZero_buffers qS layout.wordFits layout.coinFits).trans (by decide))

include layout in
theorem nameFits {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (body : Implementation .unit input output f) {buffers : Nat}
    (bound : body.program.code.memBound ≤ buffers) (fits : buffers < 2 ^ w) : body.program.savedBuffer < 2 ^ w := by
  have hw := layout.wordFits
  change max 2 body.program.code.memBound < 2 ^ w
  omega

def arguments (signing : Bool) : Implementation .unit layout.input layout.scaleArgs
    (fun value => (value.1.1, if signing then value.2.2.1 else value.2.1)) :=
  (scalarValue layout).pair (selectedPoint layout signing) (by decide) layout.wordFits
    (nameFits layout _ (scalarValue_buffers layout) (by have := layout.wordFits; omega))
    (nameFits layout _ (selectedPoint_buffers layout signing) (by have := layout.wordFits; omega))
    layout.duplicateFits (layout.fits_of_le (by rw [Layouts.input_words]; unfold Layouts.width; omega)) _

theorem arguments_buffers (signing : Bool) : (arguments layout signing).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (scalarValue_buffers layout) (selectedPoint_buffers layout signing)

end Signatures.Runtime.CaliperBackend.CoronResponse
