import Signatures.Runtime.Caliper.SchnorrAGMExtractionEntry

/-! Final-forgery entry bounds charge shape testing, flattening, lazy cache
access and deterministic rejection. The rejected branch preserves all state. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.ExtractionEntry
open Caliper BoundedSource OracleComp OracleSpec
private theorem composed_words {w : Nat} {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    (selection preparation rejection : Stmt w) (body : Interactive.Code w) (yesWords noWords : Nat) :
    ((Interactive.Code.seq (.compute selection)
      (Interactive.dispatch (.seq (.compute preparation) body) (.compute rejection) yesWords noWords)).lower port).descriptionWords =
      descriptionWords selection + descriptionWords preparation + (body.lower port).descriptionWords +
        descriptionWords rejection + 26 * yesWords + 26 * noWords + 45 := by
  change (WordIO.Code.seq (.compute selection)
    ((Interactive.dispatch (.seq (.compute preparation) body) (.compute rejection) yesWords noWords).lower port)).descriptionWords = _
  rw [WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  rw [Interactive.dispatch_descriptionWords]
  simp only [Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega

variable {w qH qS : Nat} {M F G I : Type} [Zero F] [Mul F] [Add F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : HashDispatch.Layouts w M F G qH qS) (zeroValid : layout.hash.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (port : Interactive.Port w spec)

def timeBudget (mulTime addTime sampleTime : Nat) : Nat := (Hash.prepareTime layout.hash mulTime addTime + EntryRead.timeBudget layout.hash.scheme addTime sampleTime) + 100 * layout.width + 100
def codeBudget (mulWords addWords sampleWords : Nat) : Nat := (Hash.prepareWords layout.hash mulWords addWords + EntryRead.codeBudget layout.hash.scheme addWords sampleWords) + 400 * layout.width + 600

theorem accepted_time {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.hash.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.hash.scheme.scalar.representation
      (fun _ => sampleSource) sampler) {mulTime mulWords addTime addWords sampleTime : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound port .unit layout.yes.representation
      (accepted layout zeroValid mul add mulBuffers addBuffers reserve port sampler)
      (8 * layout.hash.input.representation.encoding.words + (Hash.prepareTime layout.hash mulTime addTime + EntryRead.timeBudget layout.hash.scheme addTime sampleTime)) := by
  have packed := Interactive.TimeBound.compute (port := port) (cost := .unit)
    (prepare layout zeroValid mul add mulBuffers addBuffers reserve)
    (8 * layout.hash.input.representation.encoding.words + Hash.prepareTime layout.hash mulTime addTime)
    (fun value => Nat.add_le_add (HashDispatch.accept_time layout value)
      (Hash.prepare_time layout.hash zeroValid mul add mulBuffers addBuffers reserve mulBound addBound (layout.acceptedValue value)))
  have cached := EntryRead.time_bound layout.hash.scheme zeroValid add addBuffers ((Nat.le_add_right slots 4).trans_lt reserve)
    port sampleCorrect addBound.time_le sampleBound
  exact (packed.seq (Interactive.Refines.compute port .unit (prepare layout zeroValid mul add mulBuffers addBuffers reserve)) cached).mono (by omega)

theorem dispatch_time {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.hash.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.hash.scheme.scalar.representation
      (fun _ => sampleSource) sampler) {mulTime mulWords addTime addWords sampleTime : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound port .unit layout.selected.representation
      (dispatch layout zeroValid mul add mulBuffers addBuffers reserve port sampler)
      (Interactive.dispatchTime (w := w) .unit layout.yes.representation.encoding.words layout.no.representation.encoding.words
        (8 * layout.hash.input.representation.encoding.words + (Hash.prepareTime layout.hash mulTime addTime + EntryRead.timeBudget layout.hash.scheme addTime sampleTime))
        (8 * (EntryRead.output layout.hash.scheme).representation.encoding.words)) := by
  have acceptedBound := accepted_time layout zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect mulBound addBound sampleBound
  have rejectedBound := Interactive.TimeBound.compute (port := port) (cost := .unit) (rejected layout zeroValid)
    (8 * (EntryRead.output layout.hash.scheme).representation.encoding.words)
    (fun value => reject_time layout zeroValid ⟨value.val, value.property.1⟩)
  exact (Interactive.TimeBound.dispatch layout.yes.representation layout.no.representation acceptedBound rejectedBound
    (width_pos layout.hash.scheme.wordFits) layout.selected.representation.fits).viewInput
      layout.selected.representation (sumView layout.yes layout.no) (fun _ => rfl)

theorem time_bound {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.hash.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.hash.scheme.scalar.representation
      (fun _ => sampleSource) sampler) {mulTime mulWords addTime addWords sampleTime : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound port .unit layout.input.representation
      (code layout zeroValid mul add mulBuffers addBuffers reserve port sampler) (timeBudget layout mulTime addTime sampleTime) := by
  have selected := Interactive.TimeBound.compute (port := port) (cost := .unit) (HashDispatch.selector layout).program _ (HashDispatch.selector_bounded layout).time_le
  have branches := dispatch_time layout zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect mulBound addBound sampleBound
  have combined := selected.seq (Interactive.Refines.compute port .unit (HashDispatch.selector layout).program) branches
  apply combined.mono
  rw [Interactive.dispatchTime_unit]
  have inputSize := layout.input_le
  have hashSize := layout.hash.sizes
  have outputSize := EntryRead.output_size layout.hash.scheme
  have widths := layout.hash.width_eq
  have parts := layout.parts
  change _ + (2 + max (8 * layout.input.representation.encoding.words + _) (8 * layout.input.representation.encoding.words + _)) ≤ _
  unfold timeBudget
  omega

theorem code_bound (sampler : Interactive.Code w) {mulTime mulWords addTime addWords sampleWords : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (sampleBound : (sampler.lower port).descriptionWords ≤ sampleWords) :
    ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).descriptionWords ≤
      codeBudget layout mulWords addWords sampleWords := by
  have selected := (HashDispatch.selector_bounded layout).code_le
  have packed := HashDispatch.accept_words layout
  have flattened := Hash.prepare_words layout.hash zeroValid mul add mulBuffers addBuffers reserve mulBound addBound
  have prepared : descriptionWords (prepare layout zeroValid mul add mulBuffers addBuffers reserve).code ≤
      26 * layout.hash.input.representation.encoding.words + 14 + Hash.prepareWords layout.hash mulWords addWords + 1 := by
    change descriptionWords ((HashDispatch.accept layout).code ;; (Hash.prepare layout.hash zeroValid mul add mulBuffers addBuffers reserve).code) ≤ _
    rw [descriptionWords_seq]
    omega
  have cached := EntryRead.code_bound layout.hash.scheme zeroValid add addBuffers ((Nat.le_add_right slots 4).trans_lt reserve)
    port sampler addBound.code_le sampleBound
  have rejected := reject_words layout zeroValid
  have form := composed_words port (HashDispatch.selector layout).program.code
    (prepare layout zeroValid mul add mulBuffers addBuffers reserve).code (ExtractionEntry.rejected layout zeroValid).code
    (EntryRead.code layout.hash.scheme zeroValid add addBuffers ((Nat.le_add_right slots 4).trans_lt reserve) port sampler)
    layout.yes.representation.encoding.words layout.no.representation.encoding.words
  change ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).descriptionWords =
    descriptionWords (HashDispatch.selector layout).program.code + descriptionWords (prepare layout zeroValid mul add mulBuffers addBuffers reserve).code +
      ((EntryRead.code layout.hash.scheme zeroValid add addBuffers ((Nat.le_add_right slots 4).trans_lt reserve) port sampler).lower port).descriptionWords +
        descriptionWords (reject layout zeroValid).code + 26 * layout.input.representation.encoding.words +
          26 * layout.input.representation.encoding.words + 45 at form
  rw [form]
  have inputSize := layout.input_le
  have hashSize := layout.hash.sizes
  have outputSize := EntryRead.output_size layout.hash.scheme
  have widths := layout.hash.width_eq
  have parts := layout.parts
  unfold codeBudget
  omega

theorem names (sampler : Interactive.Code w) {sampleSlots : Nat}
    (mulNames : NamesBound mul.program.code slots) (addNames : NamesBound add.program.code slots)
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    WordIO.NamesAccounted ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port)
      (max 5 (Fresh.nameBudget slots sampleSlots)) := by
  have selected := (HashDispatch.selector_names layout).mono (Nat.le_max_left 5 (Fresh.nameBudget slots sampleSlots))
  have prepared := (HashDispatch.accept_names layout slots).seq
    (Hash.prepare_names layout.hash zeroValid mul add mulBuffers addBuffers reserve slots mulNames.accounted addNames.accounted)
  have preparedLarge := prepared.mono (show slots ≤ max 5 (Fresh.nameBudget slots sampleSlots) by unfold Fresh.nameBudget; omega)
  have acceptedBound := (WordIO.NamesAccounted.compute preparedLarge).seq
    (EntryRead.names layout.hash.scheme zeroValid add addBuffers ((Nat.le_add_right slots 4).trans_lt reserve) port sampler addNames sampleNames)
  exact (WordIO.NamesAccounted.compute selected).seq (Interactive.dispatch_names port
    («left» := accepted layout zeroValid mul add mulBuffers addBuffers reserve port sampler)
    («right» := .compute (rejected layout zeroValid).code) acceptedBound
    (WordIO.NamesAccounted.compute (reject_names layout zeroValid (max 5 (Fresh.nameBudget slots sampleSlots)))) _ _)

theorem buffers (sampler : Interactive.Code w) {sampleSlots : Nat}
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).memBound ≤
      max 11 (Fresh.nameBudget slots sampleSlots + 3) := by
  have selected := HashDispatch.selector_buffers layout
  have packed := HashDispatch.accept_buffers layout
  have flattened := Hash.prepare_buffers layout.hash zeroValid mul add mulBuffers addBuffers reserve
  have cached := EntryRead.buffers layout.hash.scheme zeroValid add addBuffers ((Nat.le_add_right slots 4).trans_lt reserve)
    port sampler addNames sampleNames
  have rejected := reject_buffers layout zeroValid
  have branches := Interactive.dispatch_buffers port (accepted layout zeroValid mul add mulBuffers addBuffers reserve port sampler)
    (.compute (ExtractionEntry.rejected layout zeroValid).code) layout.yes.representation.encoding.words layout.no.representation.encoding.words
  change ((dispatch layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).memBound ≤
    max 2 (max (max (max (HashDispatch.accept layout).code.memBound
      (Hash.prepare layout.hash zeroValid mul add mulBuffers addBuffers reserve).code.memBound)
        ((EntryRead.code layout.hash.scheme zeroValid add addBuffers ((Nat.le_add_right slots 4).trans_lt reserve) port sampler).lower port).memBound)
      (reject layout zeroValid).code.memBound) at branches
  change max (HashDispatch.selector layout).program.code.memBound ((dispatch layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).memBound ≤ _
  unfold Fresh.nameBudget at *
  omega

theorem descriptionFits (sampler : Interactive.Code w) {sampleSlots : Nat}
    (sampleFits : (sampler.lower port).DescriptionFits)
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (sampleReserve : max slots sampleSlots + 4 < 2 ^ w) :
    ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).DescriptionFits :=
  .seq layout.hash.scheme.wordFits (.compute (HashDispatch.selector layout).program.description_fits)
    (Interactive.dispatch_descriptionFits port _ _ _ _ layout.hash.scheme.wordFits
      (.seq layout.hash.scheme.wordFits (.compute (prepare layout zeroValid mul add mulBuffers addBuffers reserve).description_fits)
        (EntryRead.descriptionFits layout.hash.scheme zeroValid add addBuffers ((Nat.le_add_right slots 4).trans_lt reserve)
          port sampler sampleFits addNames sampleNames (by omega)))
      (.compute (rejected layout zeroValid).description_fits) layout.yes.representation.fits layout.no.representation.fits)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.ExtractionEntry
