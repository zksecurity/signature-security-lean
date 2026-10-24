import Proofs.Runtime.Caliper.SchnorrAGMExtractionMemory
import Proofs.Runtime.Caliper.SumContextBounds
import Proofs.Runtime.Caliper.InteractiveInvariantViews

/-! Caller exit frames keep the forgery's response next to its message, followed
by independently bounded group/row lists, union padding and the private store.
Only a returned singleton forgery needs cache admission; cutoff needs none. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerFinish
open Caliper BoundedSource
variable {w qH qS : Nat} {M F G : Type} (layout : HashDispatch.Layouts w M F G qH qS)

def data : Layout w (M × F) := layout.hash.scheme.message.prod layout.hash.scheme.scalar
  (layout.fits_of_le (by
    have := layout.scheme_le
    have := (ExtractionArithmetic.sizes layout.hash.scheme).2
    have := layout.hash.width_eq
    have := layout.parts
    omega))
def lists : Layout w (List G × List (List F)) := layout.points.prod layout.coefficients
  (layout.fits_of_le (by have := layout.parts; omega))
def forgery : Layout w ((M × F) × List G × List (List F)) := (data layout).prod (lists layout)
  (layout.fits_of_le (by
    change (layout.hash.scheme.message.representation.encoding.words + layout.hash.scheme.scalar.representation.encoding.words) +
      (layout.points.representation.encoding.words + layout.coefficients.representation.encoding.words) ≤ _
    have := layout.scheme_le
    have := (ExtractionArithmetic.sizes layout.hash.scheme).2
    have := layout.hash.width_eq
    have := layout.parts
    omega))
theorem forgery_words : (forgery layout).representation.encoding.words =
    layout.hash.scheme.message.representation.encoding.words + layout.hash.scheme.scalar.representation.encoding.words +
      layout.points.representation.encoding.words + layout.coefficients.representation.encoding.words := by
  change (_ + _) + (_ + _) = _; omega

abbrev Success := (forgery layout).Value × layout.hash.scheme.store.Value
abbrev Packet (P : Type) := ((forgery layout).Value ⊕ P) × layout.hash.scheme.store.Value

variable {P : Type} (pending : Representation w P)
    (fits : 1 + max (forgery layout).representation.encoding.words pending.encoding.words +
      layout.hash.scheme.store.representation.encoding.words < 2 ^ w)
def input : Representation w (Packet layout P) :=
  SumContext.input (forgery layout).representation pending layout.hash.scheme.store.representation
    layout.hash.scheme.wordFits fits
def returned : Representation w (Success layout) :=
  SumContext.leftFrame (forgery layout).representation pending layout.hash.scheme.store.representation fits
def cutoff : Representation w (P × layout.hash.scheme.store.Value) :=
  SumContext.rightFrame (forgery layout).representation pending layout.hash.scheme.store.representation fits
theorem frame_sizes :
    (returned layout pending fits).encoding.words =
      max (forgery layout).representation.encoding.words pending.encoding.words + layout.hash.scheme.store.representation.encoding.words ∧
    (cutoff layout pending fits).encoding.words = (returned layout pending fits).encoding.words := by
  have sizes := SumContext.frame_words (forgery layout).representation pending layout.hash.scheme.store.representation fits
  exact ⟨sizes.1, sizes.2.trans sizes.1.symm⟩
theorem choice_fits : 1 + max (returned layout pending fits).encoding.words (cutoff layout pending fits).encoding.words < 2 ^ w := by
  rw [(frame_sizes layout pending fits).2, max_self, (frame_sizes layout pending fits).1]
  omega
theorem input_bytes (value : Packet layout P) :
    ((returned layout pending fits).sum (cutoff layout pending fits) (width_pos layout.hash.scheme.wordFits)
      (choice_fits layout pending fits)).encoding.encode (SumContext.view value) =
        (input layout pending fits).encoding.encode value :=
  SumContext.sameBytes (forgery layout).representation pending layout.hash.scheme.store.representation
    layout.hash.scheme.wordFits fits value

def rawValue (value : Success layout) : HashDispatch.Input M F G × F :=
  ((value.1.val.1.1, value.1.val.2.1, value.1.val.2.2, value.2.val.2), value.1.val.1.2)

variable [DecidableEq M] [DecidableEq G]
def admitted (value : Success layout) : Prop := layout.admissible (rawValue layout value).1
instance (value : Success layout) : Decidable (admitted layout value) :=
  inferInstanceAs (Decidable (layout.admissible _))
def extractInput (value : {value : Success layout // admitted layout value}) : (Extraction.input layout).Value :=
  ⟨rawValue layout value.val, ⟨⟨value.val.1.property.1.1, value.val.1.property.2.1,
    value.val.1.property.2.2, value.val.2.property.2⟩, value.property⟩, value.val.1.property.1.2⟩
def ready (value : Packet layout P) : Prop :=
  match value.1 with | .inl forgery => admitted layout (forgery, value.2) | .inr _ => True

theorem admitted_of_room (value : Success layout) (room : value.2.val.2.1.length ≤ qH + qS) :
    admitted layout value := by
  unfold admitted HashDispatch.Layouts.admissible
  split
  · intro _; exact room
  · trivial

end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerFinish
