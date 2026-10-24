import Proofs.Runtime.Caliper.WeightedSignRouting

/-! Compute one group response, record that stored point, and return the
configuration, updated cache and logs. All retained frames are copied by code. -/
namespace Signatures.Runtime.CaliperBackend.WeightedSign
open Caliper BoundedSource
variable {w : Nat} {K M F R C G : Type} (layout : Layouts w K M F R C G)
    {respond : R × C → G} (response : Implementation .unit layout.responseInput layout.point respond)
    {slots : Nat} (responseBuffers : response.program.code.memBound ≤ slots) (reserve : slots < 2 ^ w)

include responseBuffers reserve in
theorem responseNameFits : response.program.savedBuffer < 2 ^ w := by
  have hw := layout.evaluation.cache.wordFits
  change max 2 response.program.code.memBound < 2 ^ w
  omega
def responseRetained := response.program.retain (by decide) layout.post layout.evaluation.cache.wordFits
  (responseNameFits layout response responseBuffers reserve) layout.responsePrepared.fits layout.frame.fits
theorem recordNameFits : (WeightedRecord.right layout.recorder).program.savedBuffer < 2 ^ w := by
    have bound := WeightedRecord.right_buffers layout.recorder
    have hw := layout.evaluation.cache.wordFits
    change max 2 (WeightedRecord.right layout.recorder).program.code.memBound < 2 ^ w
    omega
def recordRetained := (WeightedRecord.right layout.recorder).program.retain (by decide)
  layout.saved.representation layout.evaluation.cache.wordFits (recordNameFits layout)
  layout.recordPrepared.fits layout.recorded.fits

def completed (value : layout.evaluated.Value × layout.input.Value) : layout.output.Value :=
  finishValue layout
    (⟨WeightedRecord.rightValue (recordValue layout
      (⟨respond (responseValue layout value).val,
        response.preserves _ (responseValue layout value).property⟩, value)).val,
      (WeightedRecord.right layout.recorder).preserves _ (recordValue layout
        (⟨respond (responseValue layout value).val,
          response.preserves _ (responseValue layout value).property⟩, value)).property⟩,
      savedValue layout (⟨respond (responseValue layout value).val,
        response.preserves _ (responseValue layout value).property⟩, value))

def tail : Realizer .unit layout.post layout.output.representation (completed layout response) :=
  ((((responsePrepare layout).then (responseRetained layout response responseBuffers reserve)).then
    (recordPrepare layout)).then (recordRetained layout)).then (finish layout)

theorem completed_value (value : layout.evaluated.Value × layout.input.Value) :
    (completed layout response value).val =
      (respond (value.1.val.1, value.2.val.2.1), value.2.val.2.1, value.1.val.2,
        value.2.val.2.2.2.1, (value.2.val.1, respond (value.1.val.1, value.2.val.2.1)) :: value.2.val.2.2.2.2) := rfl

def tailTime (responseTime : Nat) : Nat :=
  8 * layout.responsePrepared.encoding.words +
  (responseTime + 8 * layout.responseInput.representation.encoding.words +
    8 * layout.point.representation.encoding.words + 12 * layout.post.encoding.words) +
  8 * layout.recordPrepared.encoding.words +
  (WeightedRecord.rightTime layout.recorder + 8 * layout.recorder.rightInput.representation.encoding.words +
    8 * layout.logs.representation.encoding.words + 12 * layout.saved.representation.encoding.words) +
  8 * layout.recorded.encoding.words
def tailWords (responseWords : Nat) : Nat :=
  (26 * layout.responsePrepared.encoding.words + 14) +
  (responseWords + 26 * layout.responseInput.representation.encoding.words +
    26 * layout.point.representation.encoding.words + 39 * layout.post.encoding.words + 39) +
  (26 * layout.recordPrepared.encoding.words + 14) +
  (WeightedRecord.rightWords layout.recorder + 26 * layout.recorder.rightInput.representation.encoding.words +
    26 * layout.logs.representation.encoding.words + 39 * layout.saved.representation.encoding.words + 39) +
  (26 * layout.recorded.encoding.words + 14) + 4

theorem tail_time {responseTime responseWords : Nat}
    (bound : response.BoundedBy responseTime responseWords) (value : layout.evaluated.Value × layout.input.Value) :
    (tail layout response responseBuffers reserve).time value ≤ tailTime layout responseTime := by
  have start := ByteRoute.time _ _ _ (responseParts layout) layout.evaluation.cache.wordFits
    (responseParts_valid layout) (responseParts_words layout) (response_bytes layout) value
  have answered := response.program.retain_time_unit_le layout.post layout.evaluation.cache.wordFits
    (responseNameFits layout response responseBuffers reserve) layout.responsePrepared.fits layout.frame.fits
      (responsePrepareValue layout value)
  have answerBound := bound.time_le (responseValue layout value)
  let frame : layout.point.Value × (layout.evaluated.Value × layout.input.Value) :=
    (⟨respond (responseValue layout value).val, response.preserves _ (responseValue layout value).property⟩, value)
  have recordedArgs := ByteRoute.time _ _ _ (recordParts layout) layout.evaluation.cache.wordFits
    (recordParts_valid layout) (recordParts_words layout) (record_bytes layout) frame
  have recorded := (WeightedRecord.right layout.recorder).program.retain_time_unit_le layout.saved.representation
    layout.evaluation.cache.wordFits (recordNameFits layout) layout.recordPrepared.fits layout.recorded.fits (recordPrepareValue layout frame)
  have recordBound := (WeightedRecord.right_bounded layout.recorder).time_le (recordValue layout frame)
  let returned : layout.logs.Value × layout.saved.Value :=
    (⟨_, (WeightedRecord.right layout.recorder).preserves _ (recordValue layout frame).property⟩, savedValue layout frame)
  have finished := Pairing.swap_time_unit_le layout.logs.representation layout.saved.representation
    layout.evaluation.cache.wordFits layout.recorded.fits returned
  change (responsePrepare layout).time value ≤ _ at start
  change (responseRetained layout response responseBuffers reserve).time (responsePrepareValue layout value) ≤
    response.program.time (responseValue layout value) + 8 * layout.responseInput.representation.encoding.words +
      8 * layout.point.representation.encoding.words + 12 * layout.post.encoding.words at answered
  change (recordPrepare layout).time frame ≤ _ at recordedArgs
  change (recordRetained layout).time (recordPrepareValue layout frame) ≤
    (WeightedRecord.right layout.recorder).program.time (recordValue layout frame) +
      8 * layout.recorder.rightInput.representation.encoding.words + 8 * layout.logs.representation.encoding.words +
      12 * layout.saved.representation.encoding.words at recorded
  change (finish layout).time returned ≤ 8 * layout.recorded.encoding.words at finished
  unfold tailTime
  change (((responsePrepare layout).time value +
    (responseRetained layout response responseBuffers reserve).time (responsePrepareValue layout value)) +
    (recordPrepare layout).time frame) +
    (recordRetained layout).time (recordPrepareValue layout frame) +
    (finish layout).time returned ≤ _
  omega

theorem tail_words {responseTime responseWords : Nat}
    (bound : response.BoundedBy responseTime responseWords) :
    descriptionWords (tail layout response responseBuffers reserve).code ≤ tailWords layout responseWords := by
  have start := ByteRoute.codeWords _ _ _ (responseParts layout) layout.evaluation.cache.wordFits
    (responseParts_valid layout) (responseParts_words layout) (response_bytes layout)
  have answered := response.program.retain_descriptionWords_le (by decide) layout.post layout.evaluation.cache.wordFits
    (responseNameFits layout response responseBuffers reserve) layout.responsePrepared.fits layout.frame.fits
  have answerBound := bound.code_le
  have recordedArgs := ByteRoute.codeWords _ _ _ (recordParts layout) layout.evaluation.cache.wordFits
    (recordParts_valid layout) (recordParts_words layout) (record_bytes layout)
  have recorded := (WeightedRecord.right layout.recorder).program.retain_descriptionWords_le (by decide)
    layout.saved.representation layout.evaluation.cache.wordFits (recordNameFits layout)
    layout.recordPrepared.fits layout.recorded.fits
  have recordBound := (WeightedRecord.right_bounded layout.recorder).code_le
  have finished := Pairing.swap_descriptionWords_le .unit (by decide) layout.logs.representation layout.saved.representation
    layout.evaluation.cache.wordFits layout.recorded.fits
  change descriptionWords (responsePrepare layout).code ≤ _ at start
  change descriptionWords (responseRetained layout response responseBuffers reserve).code ≤
    descriptionWords response.program.code + 26 * layout.responseInput.representation.encoding.words +
      26 * layout.point.representation.encoding.words + 39 * layout.post.encoding.words + 39 at answered
  change descriptionWords (recordPrepare layout).code ≤ _ at recordedArgs
  change descriptionWords (recordRetained layout).code ≤
    descriptionWords (WeightedRecord.right layout.recorder).program.code +
      26 * layout.recorder.rightInput.representation.encoding.words + 26 * layout.logs.representation.encoding.words +
      39 * layout.saved.representation.encoding.words + 39 at recorded
  change descriptionWords (finish layout).code ≤ 26 * layout.recorded.encoding.words + 14 at finished
  change descriptionWords (((((responsePrepare layout).code ;; (responseRetained layout response responseBuffers reserve).code) ;;
    (recordPrepare layout).code) ;; (recordRetained layout).code) ;; (finish layout).code) ≤ _
  simp only [descriptionWords_seq]
  unfold tailWords
  omega

theorem tail_names {names : Nat} (bound : NamesAccounted response.program.code names) :
    NamesAccounted (tail layout response responseBuffers reserve).code names :=
  ((((ByteRoute.names _ _ _ (responseParts layout) layout.evaluation.cache.wordFits
      (responseParts_valid layout) (responseParts_words layout) (response_bytes layout) names).seq
    (Retain.names bound _ _ _)).seq
    (ByteRoute.names _ _ _ (recordParts layout) layout.evaluation.cache.wordFits
      (recordParts_valid layout) (recordParts_words layout) (record_bytes layout) names)).seq
    (Retain.names (WeightedRecord.right_names layout.recorder names) _ _ _)).seq
    (Reorder.names layout.logs.representation.encoding.words layout.saved.representation.encoding.words 0 names)

end Signatures.Runtime.CaliperBackend.WeightedSign
