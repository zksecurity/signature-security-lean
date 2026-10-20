import Signatures.Runtime.Caliper.SchnorrROMTapeReadPrepare

/-! A miss appends exactly the fresh cell in chronological order. The consumed
remaining tape is retained across the draw and the append operation. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Read
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

def fresh : Constructed (drawn layout) layout.entry Prod.fst :=
  Constructed.first layout.entry (frame layout) layout.wordFits (drawn layout).representation.fits
def oldFrame : Constructed (drawn layout) (frame layout) Prod.snd :=
  Constructed.second layout.entry (frame layout) layout.wordFits (drawn layout).representation.fits
def oldSaved : Constructed (drawn layout) (saved layout) (fun value => value.2.2.2) :=
  (oldFrame layout).then (frameSaved layout)
def oldRest : Constructed (drawn layout) (list layout) (fun value => value.2.1.2.2) :=
  (oldFrame layout).then (frameRest layout)
def appendPair : Constructed (drawn layout)
    (layout.entry.prod (saved layout) (layout.fits_of_le (by have := layout.entry_le; have := saved_le layout; omega)))
    (fun value => (value.1, value.2.2.2)) :=
  (fresh layout).pair (oldSaved layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 2 < _; have := layout.wordFits; omega)
    (drawnDuplicate layout)
    (layout.fits_of_le (by have := layout.entry_le; have := drawn_le layout; omega)) _
def appendArgs : Constructed (drawn layout) (appendLayout layout).input (fun value => (value.1, value.2.2.2)) :=
  (appendPair layout).viewOutput (appendLayout layout).input
    (by
      intro value valid
      have preserved := (appendPair layout).implementation.preserves value valid
      exact ⟨⟨preserved.1, preserved.2.1⟩, preserved.2.2⟩)
    (fun _ => rfl)
def appended : Constructed (drawn layout) (list layout) (fun value => value.2.2.2 ++ [value.1]) :=
  (appendArgs layout).then (Constructed.snoc (appendLayout layout))
def savedStore : Constructed (drawn layout) (tapes layout)
    (fun value => (value.2.2.2 ++ [value.1], value.2.1.2.2)) :=
  (appended layout).pair (oldRest layout) layout.wordFits
    (by change 4 < _; have := layout.wordFits; omega) (by change 2 < _; have := layout.wordFits; omega)
    (drawnDuplicate layout)
    (layout.fits_of_le (by have := list_le layout; have := drawn_le layout; omega)) (tapes layout).representation.fits
def finish : Constructed (drawn layout) (output layout)
    (fun value => (value.1, value.2.2.2 ++ [value.1], value.2.1.2.2)) :=
  (fresh layout).pair (savedStore layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 5 < _; have := layout.wordFits; omega)
    (drawnDuplicate layout)
    (layout.fits_of_le (by have := layout.entry_le; have := drawn_le layout; omega)) (output layout).representation.fits

theorem finish_buffers : (finish layout).buffers = 6 := rfl

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Read
