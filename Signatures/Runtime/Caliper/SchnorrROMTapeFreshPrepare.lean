import Signatures.Runtime.Caliper.SchnorrROMTapeReadLayout
import Signatures.Runtime.Caliper.ConstructedArithmetic

/-! Actual raw-family routing and fresh-cell construction. Challenge cells use
tag one; private uniform draws subtract two from the requested family tag.
Literal tags and zero payloads are written by Caliper instructions. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Fresh
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

def pair := layout.counter.prod layout.counter (by change 1 + 1 < 2 ^ w; have := layout.wordFits; omega)
def choice := layout.counter.sum layout.counter (width_pos layout.wordFits)
  (by change 1 + max 1 1 < 2 ^ w; have := layout.wordFits; omega)

def tagPair (literal : Fin (2 ^ w)) : Constructed layout.counter (pair layout) (fun tag => (tag, literal.val)) :=
  (Constructed.identity layout.counter (width_pos layout.wordFits)).pair
    (Constructed.constant layout.counter layout.counter ⟨literal.val, literal.isLt⟩ layout.wordFits) layout.wordFits
    (by change 0 < _; positivity) (by change 2 < _; have := layout.wordFits; omega)
    (pair layout).representation.fits (pair layout).representation.fits (pair layout).representation.fits

def isChallenge : Constructed layout.counter layout.boolean (fun tag => decide (tag = 1)) :=
  (tagPair layout ⟨1, by have := layout.wordFits; omega⟩).then
    (Constructed.equal (2 ^ w) (2 ^ w) layout.wordFits le_rfl le_rfl)
def selector : Constructed layout.counter (choice layout)
    (fun tag => Boolean.select (decide (tag = 1), tag)) :=
  ((isChallenge layout).pair (Constructed.identity layout.counter (width_pos layout.wordFits)) layout.wordFits
    (by change 3 < _; have := layout.wordFits; omega) (by change 0 < _; positivity)
    (pair layout).representation.fits (pair layout).representation.fits (pair layout).representation.fits).then
      (Constructed.select layout.counter layout.wordFits (pair layout).representation.fits)

def dropTag : Constructed layout.counter layout.unit (fun _ => ()) :=
  Constructed.constant layout.counter layout.unit ⟨(), trivial⟩ layout.wordFits
def scalarPayload : Constructed layout.scalar layout.payload (fun answer => (answer, 0)) :=
  (Constructed.identity layout.scalar (width_pos layout.wordFits)).pair
    (Constructed.constant layout.scalar layout.counter ⟨0, by change 0 < 2 ^ w; positivity⟩ layout.wordFits) layout.wordFits
    (by change 0 < _; positivity) (by change 2 < _; have := layout.wordFits; omega)
    (layout.fits_of_le (by have := layout.entry_le; rw [Layouts.entry_words] at this; omega))
    (layout.fits_of_le (by have := layout.entry_le; rw [Layouts.entry_words] at this; omega))
    layout.payload.representation.fits
def scalarCell : Constructed layout.scalar layout.entry (fun answer => (1, answer, 0)) :=
  (Constructed.constant layout.scalar layout.counter ⟨1, by change 1 < 2 ^ w; have := layout.wordFits; omega⟩ layout.wordFits).pair
    (scalarPayload layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 3 < _; have := layout.wordFits; omega)
    (layout.fits_of_le (by have := layout.entry_le; rw [Layouts.entry_words] at this; omega))
    (layout.fits_of_le (by rw [Layouts.counter_words]; have := layout.entry_le; rw [Layouts.entry_words] at this; omega))
    layout.entry.representation.fits

def range : Constructed layout.counter layout.counter (fun tag => tag - 2) :=
  (tagPair layout ⟨2, by have := layout.wordFits; omega⟩).then
    (Constructed.subtract (2 ^ w) (2 ^ w) layout.wordFits le_rfl le_rfl)
def privateInput : Constructed layout.counter (pair layout) (fun tag => (tag - 2, tag)) :=
  (range layout).pair (Constructed.identity layout.counter (width_pos layout.wordFits)) layout.wordFits
    (by change 3 < _; have := layout.wordFits; omega) (by change 0 < _; positivity)
    (pair layout).representation.fits (pair layout).representation.fits (pair layout).representation.fits

variable [Zero F] (zeroValid : layout.scalar.valid 0)
def privatePayload : Constructed (pair layout) layout.payload (fun answer => (0, answer.1)) :=
  (Constructed.constant (pair layout) layout.scalar ⟨0, zeroValid⟩ layout.wordFits).pair
    (Constructed.first layout.counter layout.counter layout.wordFits (pair layout).representation.fits) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 2 < _; have := layout.wordFits; omega)
    (by change 2 + 2 < _; have := layout.wordFits; omega)
    (layout.fits_of_le (by
      change layout.scalar.representation.encoding.words + 2 ≤ _
      have := layout.entry_le; rw [Layouts.entry_words] at this; omega))
    layout.payload.representation.fits
def privateCell : Constructed (pair layout) layout.entry (fun answer => (answer.2, 0, answer.1)) :=
  (Constructed.second layout.counter layout.counter layout.wordFits (pair layout).representation.fits).pair
    (privatePayload layout zeroValid) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 3 < _; have := layout.wordFits; omega)
    (by change 2 + 2 < _; have := layout.wordFits; omega)
    (by change 1 + 2 < _; have := layout.wordFits; omega) layout.entry.representation.fits

omit [Zero F] in
theorem selector_buffers : (selector layout).buffers = 4 := rfl
omit [Zero F] in
theorem scalarCell_buffers : (scalarCell layout).buffers = 4 := rfl
omit [Zero F] in
theorem privateInput_buffers : (privateInput layout).buffers = 4 := rfl
theorem privateCell_buffers : (privateCell layout zeroValid).buffers = 4 := rfl

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Fresh
