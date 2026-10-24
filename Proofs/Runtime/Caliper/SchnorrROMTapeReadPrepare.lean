import Proofs.Runtime.Caliper.SchnorrROMTapeReadLayout

/-! Replay-query preparation computes the family scan and retains the original
saved tape and request. The found bit controls an executed tagged dispatch. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Read
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

def inputTag : Constructed (input layout) layout.counter Prod.fst :=
  Constructed.first layout.counter (tail layout) layout.wordFits (input layout).representation.fits
def inputTail : Constructed (input layout) (tail layout) Prod.snd :=
  Constructed.second layout.counter (tail layout) layout.wordFits (input layout).representation.fits
def inputFallback : Constructed (input layout) layout.entry (fun value => value.2.1) :=
  (inputTail layout).then (Constructed.first layout.entry (store layout) layout.wordFits (tail layout).representation.fits)
def inputStore : Constructed (input layout) (store layout) (fun value => value.2.2) :=
  (inputTail layout).then (Constructed.second layout.entry (store layout) layout.wordFits (tail layout).representation.fits)
def inputSaved : Constructed (input layout) (saved layout) (fun value => value.2.2.1) :=
  (inputStore layout).then (Constructed.first (saved layout) (list layout) layout.wordFits (store layout).representation.fits)
def inputRemaining : Constructed (input layout) (list layout) (fun value => value.2.2.2) :=
  (inputStore layout).then (Constructed.second (saved layout) (list layout) layout.wordFits (store layout).representation.fits)
def popTail : Constructed (input layout) layout.resetTail (fun value => (value.2.1, value.2.2.2)) :=
  (inputFallback layout).pair (inputRemaining layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 2 < _; have := layout.wordFits; omega)
    (inputDuplicate layout)
    (layout.fits_of_le (by have := layout.entry_le; have := input_le layout; omega)) layout.resetTail.representation.fits
def popInput : Constructed (input layout) layout.resetInput (fun value => (value.1, value.2.1, value.2.2.2)) :=
  (inputTag layout).pair (popTail layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 3 < _; have := layout.wordFits; omega)
    (inputDuplicate layout)
    (layout.fits_of_le (by rw [Layouts.counter_words]; have := input_le layout; unfold Layouts.width at *; omega))
    layout.resetInput.representation.fits
def scanned : Constructed (input layout) (Pop.state layout layout.capacity (by omega))
    (fun value => Schnorr.SeedTape.pop value.1 value.2.1 value.2.2.2) :=
  (popInput layout).then (Pop.constructed layout)
theorem scanned_buffers : (scanned layout).buffers = 6 := by
  change max (popInput layout).buffers (Pop.constructed layout).buffers = 6
  rw [Pop.constructed_buffers]
  rfl
def inputRetained : Constructed (input layout) (retained layout) (fun value => (value.1, value.2.2.1)) :=
  (inputTag layout).pair (inputSaved layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 2 < _; have := layout.wordFits; omega)
    (inputDuplicate layout)
    (layout.fits_of_le (by rw [Layouts.counter_words]; have := input_le layout; unfold Layouts.width at *; omega))
    (retained layout).representation.fits
def prepare : Constructed (input layout) (frame layout)
    (fun value => (Schnorr.SeedTape.pop value.1 value.2.1 value.2.2.2, value.1, value.2.2.1)) :=
  (scanned layout).pair (inputRetained layout) layout.wordFits
    (by change 6 < _; have := layout.wordFits; omega) (by change 3 < _; have := layout.wordFits; omega)
    (inputDuplicate layout)
    (layout.fits_of_le (by have := Pop.state_le layout layout.capacity (by omega); have := input_le layout; omega))
    (frame layout).representation.fits
theorem prepare_buffers : (prepare layout).buffers = 7 := by
  change max 2 (max (scanned layout).buffers (inputRetained layout).buffers) + 1 = 7
  rw [scanned_buffers]
  rfl

def frameScan : Constructed (frame layout) (Pop.state layout layout.capacity (by omega)) Prod.fst :=
  Constructed.first (Pop.state layout layout.capacity (by omega)) (retained layout) layout.wordFits (frame layout).representation.fits
def frameFound : Constructed (frame layout) layout.boolean (fun value => value.1.1) :=
  (frameScan layout).then (Constructed.first layout.boolean (Pop.payload layout layout.capacity (by omega))
    layout.wordFits (Pop.state layout layout.capacity (by omega)).representation.fits)
def selector : Constructed (frame layout) (choice layout) (fun value => Boolean.select (value.1.1, value)) :=
  ((frameFound layout).pair (Constructed.identity (frame layout) (width_pos layout.wordFits)) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 0 < _; positivity)
    (frameDuplicate layout) (frameTag layout) (frameTag layout)).then
      (Constructed.select (frame layout) layout.wordFits (frameTag layout))
def choose := (prepare layout).then (selector layout)
theorem choose_buffers : (choose layout).buffers = 7 := by
  change max (prepare layout).buffers (selector layout).buffers = 7
  rw [prepare_buffers]
  rfl

def frameRetained : Constructed (frame layout) (retained layout) Prod.snd :=
  Constructed.second (Pop.state layout layout.capacity (by omega)) (retained layout) layout.wordFits (frame layout).representation.fits
def frameTagValue : Constructed (frame layout) layout.counter (fun value => value.2.1) :=
  (frameRetained layout).then (Constructed.first layout.counter (saved layout) layout.wordFits (retained layout).representation.fits)
def frameSaved : Constructed (frame layout) (saved layout) (fun value => value.2.2) :=
  (frameRetained layout).then (Constructed.second layout.counter (saved layout) layout.wordFits (retained layout).representation.fits)
def frameList : Constructed (frame layout) (list layout) (fun value => value.2.2) :=
  (frameSaved layout).then (Constructed.forget (list layout) (fun cells => cells.length < layout.capacity) (width_pos layout.wordFits))
def framePayload : Constructed (frame layout) (Pop.payload layout layout.capacity (by omega)) (fun value => value.1.2) :=
  (frameScan layout).then (Constructed.second layout.boolean (Pop.payload layout layout.capacity (by omega))
    layout.wordFits (Pop.state layout layout.capacity (by omega)).representation.fits)
def frameAnswer : Constructed (frame layout) layout.entry (fun value => value.1.2.1) :=
  (framePayload layout).then (Constructed.first layout.entry (list layout) layout.wordFits (Pop.payload layout layout.capacity (by omega)).representation.fits)
def frameRest : Constructed (frame layout) (list layout) (fun value => value.1.2.2) :=
  (framePayload layout).then (Constructed.second layout.entry (list layout) layout.wordFits (Pop.payload layout layout.capacity (by omega)).representation.fits)
def hitStore : Constructed (frame layout) (tapes layout) (fun value => (value.2.2, value.1.2.2)) :=
  (frameList layout).pair (frameRest layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 2 < _; have := layout.wordFits; omega)
    (frameDuplicate layout)
    (layout.fits_of_le (by have := list_le layout; have := frame_le layout; omega))
    (tapes layout).representation.fits
def hit : Constructed (frame layout) (output layout) (fun value => (value.1.2.1, value.2.2, value.1.2.2)) :=
  (frameAnswer layout).pair (hitStore layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 3 < _; have := layout.wordFits; omega)
    (frameDuplicate layout)
    (layout.fits_of_le (by have := layout.entry_le; have := frame_le layout; omega))
    (output layout).representation.fits
def request : Constructed (frame layout) (drawInput layout) (fun value => (value.2.1, value)) :=
  (frameTagValue layout).pair (Constructed.identity (frame layout) (width_pos layout.wordFits)) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 0 < _; positivity)
    (frameDuplicate layout) (frameTag layout) (drawInput layout).representation.fits

theorem hit_buffers : (hit layout).buffers = 4 := rfl
theorem request_buffers : (request layout).buffers = 3 := rfl

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Read
