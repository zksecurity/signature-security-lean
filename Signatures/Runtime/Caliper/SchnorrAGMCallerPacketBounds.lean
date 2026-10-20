import Signatures.Runtime.Caliper.SchnorrAGMCallerPackets

/-! Costs of the executed caller packet conversions. Both branches are stored;
time charges only the selected path, including copied requests/private state. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerPackets
open Caliper BoundedSource
variable {w qH qS randomBound : Nat} {M F G : Type}
    (layout : Handler.Layouts w M F G qH qS randomBound)

theorem widths : (input layout).encoding.words ≤ width layout ∧
    (groupInput layout).encoding.words ≤ width layout ∧ (groupRaw layout).encoding.words ≤ width layout ∧
    (randomInput layout).encoding.words ≤ width layout ∧ (raw layout).encoding.words ≤ width layout ∧
    (output layout).encoding.words ≤ width layout ∧ (groupsFinished layout).encoding.words ≤ width layout ∧
    (Handler.Dispatch.randomPacket layout).encoding.words ≤ width layout ∧
    (Handler.Dispatch.groupPacket layout).encoding.words ≤ width layout ∧
    (Handler.Dispatch.groupOutput layout).encoding.words ≤ width layout := by
  change (1 + max _ (1 + max _ _) + _ ≤ _) ∧ (1 + max _ _ + _ ≤ _) ∧
    (1 + max (_ + _) (_ + _) ≤ _) ∧ (_ + _ ≤ _) ∧
    (1 + max (_ + _) (1 + max (_ + _) (_ + _)) ≤ _) ∧
    (1 + max (_ + _) (1 + max (_ + _) (_ + _)) + _ ≤ _) ∧
    (1 + max (_ + _) (_ + _) + _ ≤ _) ∧ ((_ + _) + _ ≤ _) ∧
    ((_ + _) + _ ≤ _) ∧ (1 + max ((_ + _) + _) ((_ + _) + _) ≤ _)
  unfold width
  omega

theorem prepare_time (value : Packet layout) :
    (prepare layout).time value ≤ 64 * width layout + 6 := by
  have sizes := widths layout
  have outer := SumContext.time layout.randomArgs.representation
    (groupRequest layout) layout.scheme.store.representation layout.scheme.wordFits (input layout).fits value
  change _ ≤ 24 * (input layout).encoding.words + 2 at outer
  rcases value with ⟨n | group, saved⟩
  · have tag := inl_time (randomInput layout) (groupRaw layout)
      layout.scheme.wordFits (raw layout).fits (n, saved)
    change _ ≤ 8 * (raw layout).encoding.words at tag
    change _ + (1 + (1 + ((selectSlice (w := w) 1 (randomInput layout).encoding.words).staticTime .unit + _))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
    dsimp only [Caliper.CostModel.unit] at outer tag
    dsimp only [inlRealizer, Assembly.realizer] at tag ⊢
    omega
  · have inner := SumContext.time layout.groupArgs.representation layout.groupArgs.representation
      layout.scheme.store.representation layout.scheme.wordFits (groupInput layout).fits (group, saved)
    have tag := inr_time (randomInput layout) (groupRaw layout)
      layout.scheme.wordFits (raw layout).fits (SumContext.view (group, saved))
    change _ ≤ 24 * (groupInput layout).encoding.words + 2 at inner
    change _ ≤ 8 * (raw layout).encoding.words at tag
    change _ + (1 + (1 + ((selectSlice (w := w) 1 (groupInput layout).encoding.words).staticTime .unit + (_ + _)))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
    dsimp only [Caliper.CostModel.unit] at outer inner tag
    omega

theorem prepare_words : descriptionWords (prepare layout).code ≤ 420 * width layout + 270 := by
  have sizes := widths layout
  have outer := SumContext.words layout.randomArgs.representation
    (groupRequest layout) layout.scheme.store.representation layout.scheme.wordFits (input layout).fits
  have inner := SumContext.words layout.groupArgs.representation layout.groupArgs.representation
    layout.scheme.store.representation layout.scheme.wordFits (groupInput layout).fits
  have one := inl_words (randomInput layout) (groupRaw layout)
    layout.scheme.wordFits (raw layout).fits
  have two := inr_words (randomInput layout) (groupRaw layout)
    layout.scheme.wordFits (raw layout).fits
  change _ ≤ 156 * (input layout).encoding.words + 95 at outer
  change _ ≤ 156 * (groupInput layout).encoding.words + 95 at inner
  change _ ≤ 26 * (raw layout).encoding.words + 14 at one two
  change descriptionWords (_ ;; Dispatch.code _ (_ ;; _) (randomInput layout).encoding.words
    (groupInput layout).encoding.words) ≤ _
  rw [descriptionWords_seq, Dispatch.code_descriptionWords, descriptionWords_seq]
  omega

theorem prepare_names : NamesAccounted (prepare layout).code 3 :=
  (SumContext.names layout.randomArgs.representation
    (groupRequest layout) layout.scheme.store.representation layout.scheme.wordFits (input layout).fits).seq
      (Dispatch.names (inl_names _ _ layout.scheme.wordFits (raw layout).fits).accounted
        ((SumContext.names layout.groupArgs.representation layout.groupArgs.representation layout.scheme.store.representation
          layout.scheme.wordFits (groupInput layout).fits).seq
            (inr_names _ _ layout.scheme.wordFits (raw layout).fits).accounted) _ _)


theorem randomFinish_time (value) : (randomFinish layout).time value ≤ 8 * width layout := by
  have bound := ReorderTail.time layout.random.reply.representation layout.scheme.store.representation layout.randomArgs.representation
    layout.scheme.wordFits (Handler.Dispatch.randomPacket layout).fits (productView _ _ value.1, value.2)
  have sizes := widths layout
  exact bound.trans (by change 8 * (Handler.Dispatch.randomPacket layout).encoding.words ≤ _; omega)
theorem groupFinish_time (value) : (groupFinish layout).time value ≤ 8 * width layout := by
  have bound := ReorderTail.time layout.signing.reply.representation layout.scheme.store.representation layout.groupArgs.representation
    layout.scheme.wordFits (Handler.Dispatch.groupPacket layout).fits (productView _ _ value.1, value.2)
  have sizes := widths layout
  exact bound.trans (by change 8 * (Handler.Dispatch.groupPacket layout).encoding.words ≤ _; omega)
theorem groupsFinish_time (value) : (groupsFinish layout).time value ≤ 60 * width layout + 4 := by
  have sizes := widths layout
  rcases value with value | value
  · have copied := groupFinish_time layout value
    have merged := SumContext.mergeLeft_time (groupReply layout) (groupReply layout) layout.scheme.store.representation
      layout.scheme.wordFits (groupsFinished layout).fits (groupFinishValue layout value)
    change _ ≤ 36 * (groupsFinished layout).encoding.words at merged
    change 1 + (1 + ((selectSlice (w := w) 1 (Handler.Dispatch.groupPacket layout).encoding.words).staticTime .unit + (_ + _))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
    dsimp only [Caliper.CostModel.unit] at copied merged
    omega
  · have copied := groupFinish_time layout value
    have merged := SumContext.mergeRight_time (groupReply layout) (groupReply layout) layout.scheme.store.representation
      layout.scheme.wordFits (groupsFinished layout).fits (groupFinishValue layout value)
    change _ ≤ 36 * (groupsFinished layout).encoding.words at merged
    change 1 + (1 + ((selectSlice (w := w) 1 (Handler.Dispatch.groupPacket layout).encoding.words).staticTime .unit + (_ + _))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
    dsimp only [Caliper.CostModel.unit] at copied merged
    omega
theorem finish_time (value) : (finish layout).time value ≤ 110 * width layout + 8 := by
  have sizes := widths layout
  rcases value with value | value
  · have copied := randomFinish_time layout value
    have merged := SumContext.mergeLeft_time (randomReply layout) (groupReplies layout) layout.scheme.store.representation
      layout.scheme.wordFits (output layout).fits (randomFinishValue layout value)
    change _ ≤ 36 * (output layout).encoding.words at merged
    change 1 + (1 + ((selectSlice (w := w) 1 (Handler.Dispatch.randomPacket layout).encoding.words).staticTime .unit + (_ + _))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
    dsimp only [Caliper.CostModel.unit] at copied merged
    omega
  · have copied := groupsFinish_time layout value
    have merged := SumContext.mergeRight_time (randomReply layout) (groupReplies layout) layout.scheme.store.representation
      layout.scheme.wordFits (output layout).fits (groupsFinishValue layout value)
    change _ ≤ 36 * (output layout).encoding.words at merged
    change 1 + (1 + ((selectSlice (w := w) 1 (Handler.Dispatch.groupOutput layout).encoding.words).staticTime .unit + (_ + _))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
    dsimp only [Caliper.CostModel.unit] at copied merged
    omega

theorem randomFinish_words : descriptionWords (randomFinish layout).code ≤ 26 * width layout + 14 := by
  have bound := ReorderTail.words layout.random.reply.representation layout.scheme.store.representation layout.randomArgs.representation
    layout.scheme.wordFits (Handler.Dispatch.randomPacket layout).fits
  have sizes := widths layout
  exact bound.trans (by change 26 * (Handler.Dispatch.randomPacket layout).encoding.words + 14 ≤ _; omega)
theorem groupFinish_words : descriptionWords (groupFinish layout).code ≤ 26 * width layout + 14 := by
  have bound := ReorderTail.words layout.signing.reply.representation layout.scheme.store.representation layout.groupArgs.representation
    layout.scheme.wordFits (Handler.Dispatch.groupPacket layout).fits
  have sizes := widths layout
  exact bound.trans (by change 26 * (Handler.Dispatch.groupPacket layout).encoding.words + 14 ≤ _; omega)
theorem groupsFinish_words : descriptionWords (groupsFinish layout).code ≤ 350 * width layout + 180 := by
  have copied := groupFinish_words layout
  have one := SumContext.mergeLeft_words (groupReply layout) (groupReply layout) layout.scheme.store.representation
    layout.scheme.wordFits (groupsFinished layout).fits
  have two := SumContext.mergeRight_words (groupReply layout) (groupReply layout) layout.scheme.store.representation
    layout.scheme.wordFits (groupsFinished layout).fits
  change _ ≤ 117 * (groupsFinished layout).encoding.words + 53 at one two
  change descriptionWords (Dispatch.code (_ ;; _) (_ ;; _)
    (Handler.Dispatch.groupPacket layout).encoding.words (Handler.Dispatch.groupPacket layout).encoding.words) ≤ _
  rw [Dispatch.code_descriptionWords, descriptionWords_seq, descriptionWords_seq]
  have sizes := widths layout
  omega
theorem finish_words : descriptionWords (finish layout).code ≤ 700 * width layout + 500 := by
  have random := randomFinish_words layout
  have groups := groupsFinish_words layout
  have one := SumContext.mergeLeft_words (randomReply layout) (groupReplies layout) layout.scheme.store.representation
    layout.scheme.wordFits (output layout).fits
  have two := SumContext.mergeRight_words (randomReply layout) (groupReplies layout) layout.scheme.store.representation
    layout.scheme.wordFits (output layout).fits
  change _ ≤ 117 * (output layout).encoding.words + 53 at one two
  change descriptionWords (Dispatch.code (_ ;; _) (_ ;; _)
    (Handler.Dispatch.randomPacket layout).encoding.words (Handler.Dispatch.groupOutput layout).encoding.words) ≤ _
  rw [Dispatch.code_descriptionWords, descriptionWords_seq, descriptionWords_seq]
  have sizes := widths layout
  omega

theorem randomFinish_names : NamesAccounted (randomFinish layout).code 3 := ReorderTail.names _ _ _ layout.scheme.wordFits (Handler.Dispatch.randomPacket layout).fits
theorem groupFinish_names : NamesAccounted (groupFinish layout).code 3 := ReorderTail.names _ _ _ layout.scheme.wordFits (Handler.Dispatch.groupPacket layout).fits
theorem groupsFinish_names : NamesAccounted (groupsFinish layout).code 3 :=
  Dispatch.names
    ((groupFinish_names layout).seq (Retain.names
      (inl_names (groupReply layout) (groupReply layout) layout.scheme.wordFits (groupReplies layout).fits).accounted _ _ _))
    ((groupFinish_names layout).seq (Retain.names
      (inr_names (groupReply layout) (groupReply layout) layout.scheme.wordFits (groupReplies layout).fits).accounted _ _ _)) _ _
theorem finish_names : NamesAccounted (finish layout).code 3 :=
  Dispatch.names
    ((randomFinish_names layout).seq (Retain.names
      (inl_names (randomReply layout) (groupReplies layout) layout.scheme.wordFits (reply layout).fits).accounted _ _ _))
    ((groupsFinish_names layout).seq (Retain.names
      (inr_names (randomReply layout) (groupReplies layout) layout.scheme.wordFits (reply layout).fits).accounted _ _ _)) _ _

end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerPackets
