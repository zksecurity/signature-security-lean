import Signatures.Runtime.Caliper.SchnorrROMPrivateQuery
import Signatures.Runtime.Caliper.InteractiveInvariantBounds
import Signatures.Runtime.Caliper.SynchronizesObservations

/-! The private replay query in the bounded caller's independent request,
reply and store interface. Views only reassociate identical stored bytes. The
saved-tape reservation decreases across queries and is not a runtime test. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateHandler
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} (layout : Layouts w F)

def response := ((Reply.range layout).prod layout.counter (by
  change 1 + 1 < 2 ^ w
  have := layout.wordFits
  omega)).restrict (fun value => value.2 ≤ value.1)
abbrev Request := (Reply.range layout).Value
abbrev Response := (response layout).Value
abbrev Store := (Read.tapes layout).Value
abbrev Packet := Request layout × Store layout

def input : Representation w (Packet layout) :=
  (Reply.range layout).representation.prod (Read.tapes layout).representation
    (Caller.privateInput layout).representation.fits
def output : Representation w (Response layout × Store layout) :=
  (response layout).representation.prod (Read.tapes layout).representation
    (by
      have fits := (Reply.privateOutput layout).representation.fits
      change 1 + (1 + (Read.tapes layout).representation.encoding.words) < 2 ^ w at fits
      change 1 + 1 + (Read.tapes layout).representation.encoding.words < 2 ^ w
      omega)

def ready (value : Packet layout) : Prop := value.2.val.1.length < layout.capacity
instance : DecidablePred (ready layout) := fun _ => inferInstanceAs (Decidable (_ < _))

def serviceRequest (value : Packet layout) (valid : ready layout value) : (Caller.privateInput layout).Value :=
  ⟨(value.1.val, value.2.val), value.1.property, ⟨value.2.property.1, valid⟩, value.2.property.2⟩
def finish (value : (Reply.privateOutput layout).Value) : Response layout × Store layout :=
  (⟨(value.val.1, value.val.2.1), ⟨value.property.1.1, value.property.1.2.1⟩, value.property.2⟩,
    ⟨value.val.2.2, value.property.1.2.2⟩)

theorem finish_bytes (value : (Reply.privateOutput layout).Value) :
    (output layout).encoding.encode (finish layout value) =
      (Reply.privateOutput layout).representation.encoding.encode value := by
  change (_ ++ _) ++ _ = _ ++ (_ ++ _)
  exact List.append_assoc _ _ _

def fallback (value : Packet layout) : Response layout × Store layout :=
  (⟨(value.1.val, 0), ⟨value.1.property, by change 0 < 2 ^ w; positivity⟩, Nat.zero_le _⟩, value.2)
def stored (saved : Store layout) : Schnorr.RawTape.State F := ⟨saved.val.1, saved.val.2⟩
def observed (value : Response layout × Store layout) :=
  (value.1.val.1, value.1.val.2, value.2.val)
def replyMatches (q : Request layout) (represented : Response layout) (original : Fin (q.val + 1)) : Prop :=
  represented.val = (q.val, original.val)

variable [Zero F] (zeroValid : layout.scalar.valid 0)

def source (value : Packet layout) : ProbComp (Response layout × Store layout) :=
  if valid : ready layout value then
    finish layout <$> PrivateQuery.source layout zeroValid (serviceRequest layout value valid)
  else pure (fallback layout value)

theorem refines : Interactive.RefinesOn (ready layout) (Fresh.port layout) .unit
    (input layout) (output layout) (source layout zeroValid) (PrivateQuery.code layout zeroValid) := by
  have converted := (PrivateQuery.refines layout zeroValid).viewOutput
    (output layout) (finish layout) (finish_bytes layout)
  intro tape value valid before holds
  have checked := converted tape (serviceRequest layout value valid) before holds
  simpa only [source, dite_eq_left valid] using checked

theorem time_bound : Interactive.TimeBoundOn (ready layout) (Fresh.port layout) .unit
    (input layout) (PrivateQuery.code layout zeroValid) (PrivateQuery.timeBudget layout zeroValid) := by
  intro tape value valid before holds
  exact PrivateQuery.time_bound layout zeroValid tape (serviceRequest layout value valid) before holds

theorem source_original (value : Packet layout) (valid : ready layout value) :
    observed layout <$> source layout zeroValid value =
      Caller.privateResult value.1.val <$>
        (Schnorr.RawTape.Private.oracle value.1.val).run (stored layout value.2) := by
  rw [source, dite_eq_left valid, Functor.map_map]
  exact PrivateQuery.source_eq layout zeroValid value.1.val (stored layout value.2)
    (serviceRequest layout value valid).property

theorem synchronizes (value : Packet layout) (valid : ready layout value) :
    Synchronizes (fun represented original =>
      replyMatches layout value.1 represented.1 original.1 ∧ stored layout represented.2 = original.2)
      (source layout zeroValid value)
      ((Schnorr.RawTape.Private.oracle value.1.val).run (stored layout value.2)) := by
  have joint := Synchronizes.of_map_eq (observed layout) (Caller.privateResult value.1.val)
    (source_original layout zeroValid value valid)
  apply joint.mono
  intro represented original equal
  have range := congrArg Prod.fst equal
  have answer := congrArg (fun x => x.2.1) equal
  have tapes := congrArg (fun x => x.2.2) equal
  refine ⟨Prod.ext range answer, ?_⟩
  change (represented.2.val.1, represented.2.val.2) = (original.2.saved, original.2.remaining) at tapes
  change Schnorr.LazySeed.State.mk represented.2.val.1 represented.2.val.2 = original.2
  exact congrArg (fun p => Schnorr.LazySeed.State.mk p.1 p.2) tapes

def Reserved (calls : Nat) (saved : Store layout) : Prop := saved.val.1.length + calls ≤ layout.capacity

omit [Zero F] in
theorem ready_of_reserved (value : Packet layout) {calls : Nat}
    (room : Reserved layout (calls + 1) value.2) : ready layout value := by
  unfold Reserved at room
  unfold ready
  omega

theorem reserved_after (value : Packet layout) {calls : Nat}
    (room : Reserved layout (calls + 1) value.2) (answer : Response layout × Store layout)
    (reached : answer ∈ support (source layout zeroValid value)) : Reserved layout calls answer.2 := by
  obtain ⟨original, supported, related⟩ :=
    (synchronizes layout zeroValid value (ready_of_reserved layout value room)).left_support reached
  have growth := Schnorr.RawTape.Private.oracle_growth value.1.val (stored layout value.2) original supported
  have saved := congrArg Schnorr.LazySeed.State.saved related.2
  change answer.2.val.1 = original.2.saved at saved
  unfold Reserved at *
  rw [saved]
  change original.2.saved.length ≤ value.2.val.1.length + 1 ∧ _ at growth
  omega

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateHandler
