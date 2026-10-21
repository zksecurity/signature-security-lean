import Signatures.Runtime.Caliper.SchnorrROMFreshGuardLayout
import Signatures.Runtime.Caliper.EncodedEquality

/-! The guard body executes tag tests, a saturating slot decrement and encoded
scalar comparison. Once the selected public cell is found its answer is frozen. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.FreshGuard
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {F : Type} [DecidableEq F] (layout : Layouts w F)

def context : Constructed (body layout) (tail layout) Prod.snd :=
  Constructed.second layout.entry (tail layout) layout.wordFits (body layout).representation.fits
def current : Constructed (body layout) (state layout) (fun value => value.2.1) :=
  (context layout).then (Constructed.first (state layout) layout.scalar layout.wordFits (tail layout).representation.fits)
def cell : Constructed (body layout) layout.entry Prod.fst :=
  Constructed.first layout.entry (tail layout) layout.wordFits (body layout).representation.fits
def tag : Constructed (body layout) layout.counter (fun value => value.1.1) :=
  (cell layout).then (Constructed.first layout.counter layout.payload layout.wordFits layout.entry.representation.fits)
def scalar : Constructed (body layout) layout.scalar (fun value => value.1.2.1) :=
  ((cell layout).then (Constructed.second layout.counter layout.payload layout.wordFits layout.entry.representation.fits)).then
    (Constructed.first layout.scalar layout.counter layout.wordFits layout.payload.representation.fits)
def answer : Constructed (body layout) layout.scalar (fun value => value.2.2) :=
  (context layout).then (Constructed.second (state layout) layout.scalar layout.wordFits (tail layout).representation.fits)
def count : Constructed (body layout) layout.counter (fun value => value.2.1.1) :=
  (current layout).then (Constructed.first layout.counter (flags layout) layout.wordFits (state layout).representation.fits)
def found : Constructed (body layout) layout.boolean (fun value => value.2.1.2.1) :=
  ((current layout).then (Constructed.second layout.counter (flags layout) layout.wordFits (state layout).representation.fits)).then
    (Constructed.first layout.boolean layout.boolean layout.wordFits (flags layout).representation.fits)
def natural (n : Nat) (fits : n < 2 ^ w) : Constructed (body layout) layout.counter (fun _ => n) :=
  Constructed.constant (body layout) layout.counter ⟨n, fits⟩ layout.wordFits

/-- All body products are emitted copies with a fixed scratch reserve. -/
def combine {A B : Type} {leftOutput : Layout w A} {rightOutput : Layout w B}
    {f : Schnorr.TapeCell F × (Accumulator × F) → A} {g : Schnorr.TapeCell F × (Accumulator × F) → B}
    (first : Constructed (body layout) leftOutput f) (second : Constructed (body layout) rightOutput g)
    (leftBuffers : first.buffers ≤ 8) (rightBuffers : second.buffers ≤ 8)
    (leftSize : leftOutput.representation.encoding.words ≤ layout.scalar.representation.encoding.words + 6)
    (rightSize : rightOutput.representation.encoding.words ≤ layout.scalar.representation.encoding.words + 6) :=
  first.pair second layout.wordFits
    (by have := layout.wordFits; omega) (by have := layout.wordFits; omega) (duplicate layout)
    (layout.fits_of_le (by have := (sizes layout).2.1; have := width_min layout; omega))
    (layout.fits_of_le (by have := width_min layout; omega))

def scalarPair := layout.scalar.prod layout.scalar (layout.fits_of_le (by have := width_min layout; omega))
def scalarEquality : Constructed (scalarPair layout) layout.boolean (fun value => decide (value.1 = value.2)) where
  implementation := EncodedEquality.implementation .unit layout.scalar layout.wordFits (scalarPair layout).representation.fits
  budget := ⟨6 * layout.scalar.representation.encoding.words + 3, 30 * layout.scalar.representation.encoding.words + 13⟩
  bounded := EncodedEquality.implementation_boundedBy _ _ _
  buffers := 5
  buffers_le := (EncodedEquality.implementation_names .unit _ _ _).buffers
  names slots := (EncodedEquality.implementation_names .unit _ _ _).mono (by
    change 5 ≤ slots + descriptionWords (EncodedEquality.code (w := w) layout.scalar.representation.encoding.words)
    rw [EncodedEquality.code_descriptionWords]
    omega)
def equal := (combine layout (scalar layout) (answer layout) (by change 2 ≤ 8; decide) (by change 2 ≤ 8; decide) (by omega) (by omega)).then (scalarEquality layout)
def arguments {f : Schnorr.TapeCell F × (Accumulator × F) → Nat}
    (get : Constructed (body layout) layout.counter f) (buffers : get.buffers ≤ 8) (n : Nat) (fits : n < 2 ^ w) :=
  combine layout get (natural layout n fits) buffers (by change 2 ≤ 8; decide)
    (by change 1 ≤ _; omega) (by change 1 ≤ _; omega)
def isPublic := (arguments layout (tag layout) (by change 2 ≤ 8; decide) 1 (by have := layout.wordFits; omega)).then
  (Constructed.equal (2 ^ w) (2 ^ w) layout.wordFits le_rfl le_rfl)
def isZero := (arguments layout (count layout) (by change 2 ≤ 8; decide) 0 (by positivity)).then
  (Constructed.equal (2 ^ w) (2 ^ w) layout.wordFits le_rfl le_rfl)
def decrement := (arguments layout (count layout) (by change 2 ≤ 8; decide) 1 (by have := layout.wordFits; omega)).then
  (Constructed.subtract (2 ^ w) (2 ^ w) layout.wordFits le_rfl le_rfl)
def yes := Constructed.constant (body layout) layout.boolean ⟨true, trivial⟩ layout.wordFits
def selectedFlags := combine layout (yes layout) (equal layout) (by change 2 ≤ 8; decide) (by change 5 ≤ 8; decide)
  (by change 1 ≤ _; omega) (by change 1 ≤ _; omega)
def hit := combine layout (natural layout 0 (by positivity)) (selectedFlags layout) (by change 2 ≤ 8; decide) (by change 6 ≤ 8; decide)
  (by change 1 ≤ _; omega) (by change 2 ≤ _; omega)
def pendingFlags := Constructed.constant (body layout) (flags layout) ⟨(false, false), trivial, trivial⟩ layout.wordFits
def miss := combine layout (decrement layout) (pendingFlags layout) (by change 3 ≤ 8; decide) (by change 2 ≤ 8; decide)
  (by change 1 ≤ _; omega) (by change 2 ≤ _; omega)
def publicStep := Constructed.branch layout.wordFits (isZero layout) (hit layout) (miss layout)
  (by change 3 < _; have := layout.wordFits; omega) (duplicate layout) (tagged layout)
def searching := Constructed.branch layout.wordFits (isPublic layout) (publicStep layout) (current layout)
  (by change 3 < _; have := layout.wordFits; omega) (duplicate layout) (tagged layout)
def stepConstructed : Constructed (body layout) (state layout) step :=
  (Constructed.branch layout.wordFits (found layout) (current layout) (searching layout)
    (by change 2 < _; have := layout.wordFits; omega) (duplicate layout) (tagged layout)).castFunction (by
      funext value
      simp only [Function.comp_apply, step, decide_eq_true_eq])
theorem equal_buffers : (equal layout).buffers = 5 := rfl
theorem selectedFlags_buffers : (selectedFlags layout).buffers = 6 := by
  change max 2 (max 2 (equal layout).buffers) + 1 = 6
  rw [equal_buffers]
  decide
theorem hit_buffers : (hit layout).buffers = 7 := by
  change max 2 (max 2 (selectedFlags layout).buffers) + 1 = 7
  rw [selectedFlags_buffers]
  decide
theorem publicStep_buffers : (publicStep layout).buffers = 7 := by
  change max (max 2 3 + 1) (max (hit layout).buffers 4) = 7
  rw [hit_buffers]
  decide
theorem searching_buffers : (searching layout).buffers = 7 := by
  change max (max 2 3 + 1) (max (publicStep layout).buffers 2) = 7
  rw [publicStep_buffers]
  decide
theorem body_buffers : (stepConstructed layout).buffers = 7 := by
  change max (max 2 2 + 1) (max 2 (searching layout).buffers) = 7
  rw [searching_buffers]
  decide

end Signatures.Runtime.CaliperBackend.SchnorrROM.FreshGuard
