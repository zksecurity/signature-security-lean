import Proofs.Runtime.Caliper.SchnorrROMCallerAdmission
import Proofs.Runtime.Caliper.SumContextMergeBuffers
import Proofs.Runtime.Caliper.StatefulCacheBuffers

/-! Costs of converting the caller's independent packets to the service frame
and back. Padding and private-state copies execute and all branches are stored. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.CallerPackets
open Caliper BoundedSource
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

theorem widths : (input config).encoding.words ≤ width config ∧
    (innerInput config).encoding.words ≤ width config ∧ (innerRaw config).encoding.words ≤ width config ∧
    (signingRaw config).encoding.words ≤ width config ∧ (raw config).encoding.words ≤ width config ∧
    (output config).encoding.words ≤ width config ∧ (innerFinished config).encoding.words ≤ width config ∧
    (Handler.innerOutput config).encoding.words ≤ width config ∧
    config.handler.output.representation.encoding.words ≤ width config := by
  change (1 + max (1 + max _ _) _ + _ ≤ _) ∧ (1 + max _ _ + _ ≤ _) ∧
    (1 + max (_ + _) (_ + _) ≤ _) ∧ (_ + _ ≤ _) ∧
    (1 + max (1 + max (_ + _) (_ + _)) (_ + _) ≤ _) ∧
    (1 + max (1 + max _ _) _ + _ ≤ _) ∧ (1 + max _ _ + _ ≤ _) ∧
    (1 + max (_ + _) (_ + _) ≤ _) ∧ (_ + _ ≤ _)
  unfold width
  dsimp only [randomRequest, hashRequest, signingRequest, randomReply, hashReply, signingReply, stored]
  omega

theorem prepare_time (value : Packet config) : (prepare config).time value ≤ 64 * width config + 6 := by
  have sizes := widths config
  have outer := SumContext.time (innerRequest config) (signingRequest config) (stored config)
    config.sampler.wordFits (input config).fits value
  change _ ≤ 24 * (input config).encoding.words + 2 at outer
  rcases value with ⟨inner | message, saved⟩
  · have copied := SumContext.time (randomRequest config) (hashRequest config) (stored config)
      config.sampler.wordFits (innerInput config).fits (inner, saved)
    have tag := inl_time (innerRaw config) (signingRaw config) config.sampler.wordFits (raw config).fits
      (SumContext.view (inner, saved))
    change _ ≤ 24 * (innerInput config).encoding.words + 2 at copied
    change _ ≤ 8 * (raw config).encoding.words at tag
    change _ + (1 + (1 + ((selectSlice (w := w) 1 (innerInput config).encoding.words).staticTime .unit + (_ + _)))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
    dsimp only [Caliper.CostModel.unit] at outer copied tag
    omega
  · have tag := inr_time (innerRaw config) (signingRaw config) config.sampler.wordFits (raw config).fits (message, saved)
    change _ ≤ 8 * (raw config).encoding.words at tag
    change _ + (1 + (1 + ((selectSlice (w := w) 1 (signingRaw config).encoding.words).staticTime .unit + _))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
    dsimp only [Caliper.CostModel.unit] at outer tag
    dsimp only [inrRealizer, Assembly.realizer] at tag ⊢
    omega

theorem prepare_words : descriptionWords (prepare config).code ≤ 420 * width config + 270 := by
  have sizes := widths config
  have outer := SumContext.words (innerRequest config) (signingRequest config) (stored config) config.sampler.wordFits (input config).fits
  have inner := SumContext.words (randomRequest config) (hashRequest config) (stored config) config.sampler.wordFits (innerInput config).fits
  have one := inl_words (innerRaw config) (signingRaw config) config.sampler.wordFits (raw config).fits
  have two := inr_words (innerRaw config) (signingRaw config) config.sampler.wordFits (raw config).fits
  change _ ≤ 156 * (input config).encoding.words + 95 at outer
  change _ ≤ 156 * (innerInput config).encoding.words + 95 at inner
  change _ ≤ 26 * (raw config).encoding.words + 14 at one two
  change descriptionWords (_ ;; Dispatch.code (_ ;; _) _ (innerInput config).encoding.words (signingRaw config).encoding.words) ≤ _
  rw [descriptionWords_seq, Dispatch.code_descriptionWords, descriptionWords_seq]
  omega

theorem prepare_names : NamesAccounted (prepare config).code 3 :=
  (SumContext.names (innerRequest config) (signingRequest config) (stored config) config.sampler.wordFits (input config).fits).seq
    (Dispatch.names
      ((SumContext.names (randomRequest config) (hashRequest config) (stored config) config.sampler.wordFits (innerInput config).fits).seq
        (inl_names _ _ config.sampler.wordFits (raw config).fits).accounted)
      (inr_names _ _ config.sampler.wordFits (raw config).fits).accounted _ _)

theorem prepare_buffers : (prepare config).code.memBound ≤ 3 := by
  have outer := SumContext.buffers (innerRequest config) (signingRequest config) (stored config)
    config.sampler.wordFits (input config).fits
  have inner := SumContext.buffers (randomRequest config) (hashRequest config) (stored config)
    config.sampler.wordFits (innerInput config).fits
  have one := (inl_names (innerRaw config) (signingRaw config) config.sampler.wordFits (raw config).fits).buffers
  have two := (inr_names (innerRaw config) (signingRaw config) config.sampler.wordFits (raw config).fits).buffers
  change max _ (Dispatch.code _ _ _ _).memBound ≤ 3
  apply max_le outer
  apply (Dispatch.buffers _ _ _ _).trans
  change max 2 (max (max _ _) _) ≤ 3
  omega

theorem innerFinish_time (value) : (innerFinish config).time value ≤ 44 * width config + 2 := by
  have bound := SumContext.merge_time (randomReply config) (hashReply config) (stored config)
    config.sampler.wordFits (innerFinished config).fits (innerReplyView config value)
  have sizes := widths config
  exact bound.trans (by change 44 * (innerFinished config).encoding.words + 2 ≤ _; omega)
theorem finish_time (value) : (finish config).time value ≤ 90 * width config + 6 := by
  have sizes := widths config
  cases value with
  | inl value =>
    have copied := innerFinish_time config value
    have merged := SumContext.mergeLeft_time (innerReply config) (signingReply config) (stored config)
      config.sampler.wordFits (output config).fits (innerFinishedValue config value)
    change _ ≤ 36 * (output config).encoding.words at merged
    change 1 + (1 + ((selectSlice (w := w) 1 (Handler.innerOutput config).encoding.words).staticTime .unit + (_ + _))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
    dsimp only [Caliper.CostModel.unit] at copied merged
    omega
  | inr value =>
    have merged := SumContext.mergeRight_time (innerReply config) (signingReply config) (stored config)
      config.sampler.wordFits (output config).fits (productView config.handler.core.reply config.handler.store value)
    change _ ≤ 36 * (output config).encoding.words at merged
    change 1 + (1 + ((selectSlice (w := w) 1 config.handler.output.representation.encoding.words).staticTime .unit + _)) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
    dsimp only [Caliper.CostModel.unit] at merged
    dsimp only [Realizer.viewInput]
    omega

theorem innerFinish_words : descriptionWords (innerFinish config).code ≤ 286 * width config + 143 := by
  have bound := SumContext.merge_words (randomReply config) (hashReply config) (stored config) config.sampler.wordFits (innerFinished config).fits
  have sizes := widths config
  exact bound.trans (by change 286 * (innerFinished config).encoding.words + 143 ≤ _; omega)
theorem finish_words : descriptionWords (finish config).code ≤ 600 * width config + 310 := by
  have copied := innerFinish_words config
  have one := SumContext.mergeLeft_words (innerReply config) (signingReply config) (stored config) config.sampler.wordFits (output config).fits
  have two := SumContext.mergeRight_words (innerReply config) (signingReply config) (stored config) config.sampler.wordFits (output config).fits
  change _ ≤ 117 * (output config).encoding.words + 53 at one two
  change descriptionWords (Dispatch.code (_ ;; _) _ (Handler.innerOutput config).encoding.words
    config.handler.output.representation.encoding.words) ≤ _
  rw [Dispatch.code_descriptionWords, descriptionWords_seq]
  dsimp only [Realizer.viewInput]
  have sizes := widths config
  omega

theorem finish_names : NamesAccounted (finish config).code 3 :=
  Dispatch.names
    ((SumContext.merge_names (randomReply config) (hashReply config) (stored config) config.sampler.wordFits (innerFinished config).fits).seq
      (Retain.names (inl_names (innerReply config) (signingReply config) config.sampler.wordFits (reply config).fits).accounted _ _ _))
    (Retain.names (inr_names (innerReply config) (signingReply config) config.sampler.wordFits (reply config).fits).accounted _ _ _) _ _
theorem finish_buffers : (finish config).code.memBound ≤ 4 := by
  have copied := SumContext.merge_buffers (randomReply config) (hashReply config) (stored config) config.sampler.wordFits (innerFinished config).fits
  have one := SumContext.mergeLeft_buffers (innerReply config) (signingReply config) (stored config) config.sampler.wordFits (output config).fits
  have two := SumContext.mergeRight_buffers (innerReply config) (signingReply config) (stored config) config.sampler.wordFits (output config).fits
  change (Dispatch.code _ _ _ _).memBound ≤ 4
  apply (Dispatch.buffers _ _ _ _).trans
  change max 2 (max (max (innerFinish config).code.memBound _)
    (SumContext.mergeRight (innerReply config) (signingReply config) (stored config)
      config.sampler.wordFits (output config).fits).code.memBound) ≤ 4
  change (innerFinish config).code.memBound ≤ 4 at copied
  omega

end Signatures.Runtime.CaliperBackend.SchnorrROM.CallerPackets
