import Signatures.Runtime.Caliper.ListFixedCons
import Signatures.Runtime.Caliper.ReorderTail
import Signatures.Runtime.Caliper.ImplementationMemory
import Signatures.Runtime.WeightedReply

/-! Fixed-capacity reply-log updates with an independently typed saved value.
For weighted signatures the saved value is the other reply log. Both orders
are implemented by paid retention and copying, allowing hash indices and
signing messages to have different types and encoded widths. -/
namespace Signatures.Runtime.CaliperBackend.WeightedRecord
open Caliper BoundedSource

structure Layouts (w : Nat) (A S : Type) where
  entry : Layout w A
  saved : Layout w S
  capacityPred : Nat
  wordFits : 16 < 2 ^ w
  countFits : capacityPred + 1 < 2 ^ w
  storageFits : 4 * (entry.representation.encoding.words +
    (1 + (capacityPred + 1) * entry.representation.encoding.words) +
    saved.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {A S : Type} (layout : Layouts w A S)
def logWords : Nat := 1 + (layout.capacityPred + 1) * layout.entry.representation.encoding.words
def width : Nat := layout.entry.representation.encoding.words + layout.logWords + layout.saved.representation.encoding.words
theorem fits_of_le {words : Nat} (bound : words ≤ 4 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits
def log := layout.entry.boundedList (layout.capacityPred + 1) layout.countFits
  (layout.fits_of_le (by change layout.logWords ≤ _; unfold width; omega))
def leftOutput : Layout w (List A × S) := layout.log.prod layout.saved
  (layout.fits_of_le (by change layout.logWords + _ ≤ _; unfold width; omega))
def rightOutput : Layout w (S × List A) := layout.saved.prod layout.log
  (layout.fits_of_le (by change _ + layout.logWords ≤ _; unfold width; omega))
def leftRaw : Layout w (A × (List A × S)) := layout.entry.prod layout.leftOutput
  (layout.fits_of_le (by change _ + (layout.logWords + _) ≤ _; unfold width; omega))
def rightRaw : Layout w (A × (S × List A)) := layout.entry.prod layout.rightOutput
  (layout.fits_of_le (by change _ + (_ + layout.logWords) ≤ _; unfold width; omega))
def leftRoom (value : A × (List A × S)) : Prop := value.2.1.length ≤ layout.capacityPred
def rightRoom (value : A × (S × List A)) : Prop := value.2.2.length ≤ layout.capacityPred
instance : DecidablePred layout.leftRoom := fun _ => inferInstanceAs (Decidable (_ ≤ _))
instance : DecidablePred layout.rightRoom := fun _ => inferInstanceAs (Decidable (_ ≤ _))
def leftInput := layout.leftRaw.restrict layout.leftRoom
def rightInput := layout.rightRaw.restrict layout.rightRoom
theorem consFits : 1 + (layout.capacityPred + 2) * layout.entry.representation.encoding.words < 2 ^ w := by
  apply layout.fits_of_le
  unfold width logWords
  nlinarith
def cons := ListData.fixedCons .unit (by decide) layout.entry layout.capacityPred
  layout.wordFits layout.countFits layout.consFits
theorem consBuffers : layout.cons.program.code.memBound ≤ 2 := ListData.fixedCons_buffers _ _ _ _ _ _ _
theorem consNameFits : layout.cons.program.savedBuffer < 2 ^ w := by
  have := layout.consBuffers
  have := layout.wordFits
  unfold Realizer.savedBuffer
  omega
theorem consFrameFits : (layout.entry.representation.encoding.words + layout.logWords) +
    layout.saved.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by unfold width; omega)
theorem switchFits : layout.entry.representation.encoding.words + layout.saved.representation.encoding.words +
    layout.log.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by change _ + _ + layout.logWords ≤ _; unfold width; omega)
theorem inputWords : layout.leftInput.representation.encoding.words = layout.width := by
  change _ + (layout.logWords + _) = _; unfold width; omega
theorem rightInputWords : layout.rightInput.representation.encoding.words = layout.width := by
  change _ + (_ + layout.logWords) = _; unfold width; omega
theorem outputWords : layout.leftOutput.representation.encoding.words =
    layout.logWords + layout.saved.representation.encoding.words := rfl
theorem rightOutputWords : layout.rightOutput.representation.encoding.words =
    layout.saved.representation.encoding.words + layout.logWords := rfl
end Layouts

variable {w : Nat} {A S : Type} (layout : Layouts w A S)
def leftValue (value : A × (List A × S)) : List A × S := (value.1 :: value.2.1, value.2.2)
def rightValue (value : A × (S × List A)) : S × List A := (value.2.1, value.1 :: value.2.2)

theorem preserves (value : A × (List A × S)) (valid : layout.leftInput.valid value) :
    layout.leftOutput.valid (leftValue value) := by
  refine ⟨⟨by change (value.1 :: value.2.1).length ≤ _; simp only [List.length_cons]; exact Nat.succ_le_succ valid.2, ?_⟩,
    valid.1.2.2⟩
  intro entry member
  rcases List.mem_cons.mp member with rfl | member
  · exact valid.1.1
  · exact valid.1.2.1.2 entry member

def arguments (value : layout.leftInput.Value) :
    (ListData.fixedConsInput layout.entry layout.capacityPred layout.countFits layout.consFits).Value × layout.saved.Value :=
  (⟨(value.val.1, value.val.2.1), ⟨value.property.1.1, value.property.1.2.1⟩, value.property.2⟩,
    ⟨value.val.2.2, value.property.1.2.2⟩)

def retained := layout.cons.program.retain (by decide) layout.saved.representation layout.wordFits layout.consNameFits
  layout.consFrameFits
  layout.leftOutput.representation.fits

def left : Implementation .unit layout.leftInput layout.leftOutput leftValue where
  preserves := preserves layout
  program := ((retained layout).viewInput layout.leftInput.representation (arguments layout) (by
    intro value
    exact (List.append_assoc
      (layout.entry.representation.encoding.encode ⟨value.val.1, value.property.1.1⟩)
      (layout.log.representation.encoding.encode ⟨value.val.2.1, value.property.1.2.1⟩)
      (layout.saved.representation.encoding.encode ⟨value.val.2.2, value.property.1.2.2⟩)).symm)).viewOutput layout.leftOutput.representation
      (fun value => ⟨leftValue value.val, preserves layout value.val value.property⟩) (fun _ => rfl)

def switch : Implementation .unit layout.rightInput layout.leftInput
    (fun value => (value.1, value.2.2, value.2.1)) where
  preserves _ valid := ⟨⟨valid.1.1, valid.1.2.2, valid.1.2.1⟩, valid.2⟩
  program := ((ReorderTail.realizer layout.entry.representation layout.saved.representation layout.log.representation
    layout.wordFits layout.switchFits).viewInput
      layout.rightInput.representation
      (fun value => ((⟨value.val.1, value.property.1.1⟩, ⟨value.val.2.1, value.property.1.2.1⟩),
        ⟨value.val.2.2, value.property.1.2.2⟩))
      (fun value => (List.append_assoc
        (layout.entry.representation.encoding.encode ⟨value.val.1, value.property.1.1⟩)
        (layout.saved.representation.encoding.encode ⟨value.val.2.1, value.property.1.2.1⟩)
        (layout.log.representation.encoding.encode ⟨value.val.2.2, value.property.1.2.2⟩)).symm)).viewOutput layout.leftInput.representation
        (fun value => ⟨(value.val.1, value.val.2.2, value.val.2.1),
          ⟨value.property.1.1, value.property.1.2.2, value.property.1.2.1⟩, value.property.2⟩)
        (fun value => (List.append_assoc
          (layout.entry.representation.encoding.encode ⟨value.val.1, value.property.1.1⟩)
          (layout.log.representation.encoding.encode ⟨value.val.2.2, value.property.1.2.2⟩)
          (layout.saved.representation.encoding.encode ⟨value.val.2.1, value.property.1.2.1⟩)).symm)

def swap : Implementation .unit layout.leftOutput layout.rightOutput Prod.swap where
  preserves _ valid := ⟨valid.2, valid.1⟩
  program := ((Pairing.swap .unit (by decide) layout.log.representation layout.saved.representation
    layout.wordFits layout.leftOutput.representation.fits).viewInput layout.leftOutput.representation
      (productView layout.log layout.saved) (fun _ => rfl)).viewOutput layout.rightOutput.representation
        (fun value => ⟨value.val.swap, value.property.2, value.property.1⟩) (fun _ => rfl)

def right : Implementation .unit layout.rightInput layout.rightOutput rightValue :=
  ((switch layout).then (left layout)).then (swap layout)

theorem left_buffers : (left layout).program.code.memBound ≤ 3 := by
  have bound := (Retain.code_names layout.cons.program.code layout.cons.program.savedBuffer
    (layout.entry.representation.encoding.words + layout.logWords) layout.logWords
    layout.saved.representation.encoding.words (Nat.le_max_left _ _) (Nat.le_max_right _ _)).2
  have small := layout.consBuffers
  change (left layout).program.code.memBound ≤ layout.cons.program.savedBuffer + 1 at bound
  unfold Realizer.savedBuffer at bound
  omega

theorem right_buffers : (right layout).program.code.memBound ≤ 3 :=
  max_le (max_le
    (((Assembly.code_names _ 1 (ReorderTail.sources layout.entry.representation.encoding.words
      layout.saved.representation.encoding.words layout.log.representation.encoding.words)).2 :
        (switch layout).program.code.memBound ≤ 2).trans (by decide))
    (left_buffers layout)) ((Reorder.buffers layout.log.representation.encoding.words layout.saved.representation.encoding.words 0).trans (by decide))

def leftTime : Nat := 8 * layout.entry.representation.encoding.words + 32 * layout.logWords +
  12 * layout.saved.representation.encoding.words + 5
def leftWords : Nat := 26 * layout.entry.representation.encoding.words + 104 * layout.logWords +
  39 * layout.saved.representation.encoding.words + 92
def rightTime : Nat := leftTime layout + 16 * layout.width
def rightWords : Nat := leftWords layout + 52 * layout.width + 30

theorem left_bounded : (left layout).BoundedBy (leftTime layout) (leftWords layout) := by
  have consBound := ListData.fixedCons_boundedBy layout.entry layout.capacityPred layout.wordFits
    layout.countFits layout.consFits
  constructor
  · intro value
    have copied := layout.cons.program.retain_time_unit_le layout.saved.representation layout.wordFits
      layout.consNameFits layout.consFrameFits layout.leftOutput.representation.fits (arguments layout value)
    have body := consBound.time_le (arguments layout value).1
    change (left layout).program.time value ≤ layout.cons.program.time (arguments layout value).1 +
      8 * (layout.entry.representation.encoding.words + layout.logWords) + 8 * layout.logWords +
      12 * layout.saved.representation.encoding.words at copied
    change layout.cons.program.time (arguments layout value).1 ≤ 16 * layout.logWords + 5 at body
    unfold leftTime
    omega
  · have copied := layout.cons.program.retain_descriptionWords_le (by decide) layout.saved.representation
      layout.wordFits layout.consNameFits layout.consFrameFits layout.leftOutput.representation.fits
    have body := consBound.code_le
    change descriptionWords (left layout).program.code ≤ descriptionWords layout.cons.program.code +
      26 * (layout.entry.representation.encoding.words + layout.logWords) + 26 * layout.logWords +
      39 * layout.saved.representation.encoding.words + 39 at copied
    change descriptionWords layout.cons.program.code ≤ 52 * layout.logWords + 53 at body
    unfold leftWords
    omega

theorem switch_bounded : (switch layout).BoundedBy (8 * layout.width) (26 * layout.width + 14) := by
  constructor
  · intro value
    exact (ReorderTail.time layout.entry.representation layout.saved.representation layout.log.representation
      layout.wordFits layout.switchFits
      ((⟨value.val.1, value.property.1.1⟩, ⟨value.val.2.1, value.property.1.2.1⟩),
        ⟨value.val.2.2, value.property.1.2.2⟩)).trans (by
      change 8 * (layout.entry.representation.encoding.words + layout.saved.representation.encoding.words + layout.logWords) ≤ _
      unfold Layouts.width; omega)
  · exact (ReorderTail.words layout.entry.representation layout.saved.representation layout.log.representation
      layout.wordFits layout.switchFits).trans (by
      change 26 * (layout.entry.representation.encoding.words + layout.saved.representation.encoding.words + layout.logWords) + 14 ≤ _
      unfold Layouts.width; omega)

theorem swap_bounded : (swap layout).BoundedBy (8 * layout.width) (26 * layout.width + 14) := by
  constructor
  · intro value
    exact (Pairing.swap_time_unit_le layout.log.representation layout.saved.representation
      layout.wordFits layout.leftOutput.representation.fits (productView layout.log layout.saved value)).trans (by
      change 8 * (layout.logWords + layout.saved.representation.encoding.words) ≤ _
      unfold Layouts.width; omega)
  · exact (Pairing.swap_descriptionWords_le .unit (by decide) layout.log.representation layout.saved.representation
      layout.wordFits layout.leftOutput.representation.fits).trans (by
      change 26 * (layout.logWords + layout.saved.representation.encoding.words) + 14 ≤ _
      unfold Layouts.width; omega)

theorem right_bounded : (right layout).BoundedBy (rightTime layout) (rightWords layout) := by
  apply (((switch_bounded layout).then (left_bounded layout)).then (swap_bounded layout)).mono
  · unfold rightTime; omega
  · unfold rightWords; omega

theorem left_names (slots : Nat) : NamesAccounted (left layout).program.code slots :=
  Retain.names (ListData.fixedCons_names layout.entry layout.capacityPred layout.wordFits layout.countFits layout.consFits slots) _ _ _
theorem right_names (slots : Nat) : NamesAccounted (right layout).program.code slots :=
  ((Assembly.code_namesAccounted _ slots (ReorderTail.sources layout.entry.representation.encoding.words
    layout.saved.representation.encoding.words layout.log.representation.encoding.words)).seq (left_names layout slots)).seq
    (Reorder.names layout.log.representation.encoding.words layout.saved.representation.encoding.words 0 slots)

theorem hash_source {K M G : Type} (request : K) (reply : G)
    (logs : Model.LazyAGM.Transcript K M G) :
    leftValue ((request, reply), logs) = WeightedAGM.Reply.record (.inl request) reply logs := rfl
theorem sign_source {K M G : Type} (request : M) (reply : G)
    (logs : Model.LazyAGM.Transcript K M G) :
    rightValue ((request, reply), logs) = WeightedAGM.Reply.record (.inr request) reply logs := rfl

end Signatures.Runtime.CaliperBackend.WeightedRecord
