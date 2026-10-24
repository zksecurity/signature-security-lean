import Proofs.Runtime.Caliper.SchnorrAGMHandlerHash

/-! Hash wrapper overhead includes both permutations, the saved configuration,
and construction of the empty group reply. Core costs remain explicit. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.HashComponent
open Caliper BoundedSource OracleComp OracleSpec
private theorem composed_words {w : Nat} {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    (preparation wrapping : Stmt w) (body : Interactive.Code w) :
    ((Interactive.Code.seq (.compute preparation) (.seq body (.compute wrapping))).lower port).descriptionWords =
      descriptionWords preparation + (body.lower port).descriptionWords + descriptionWords wrapping + 4 := by
  simp only [Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega

variable {w qH qS randomBound : Nat} {M F G I : Type}
    (layout : Handler.Layouts w M F G qH qS randomBound)
theorem prepared_le [DecidableEq M] [DecidableEq G] : layout.hashPrepared.encoding.words ≤ 2 * layout.width := by
  change layout.hash.input.representation.encoding.words + layout.scheme.config.representation.encoding.words ≤ _
  have := layout.hash.input_le; have := layout.core_widths; have := layout.config_le; omega
def timeBudget (mulTime addTime sampleTime : Nat) : Nat :=
  HashDispatch.timeBudget layout.hash mulTime addTime sampleTime + 64 * layout.width
def codeBudget (mulWords addWords sampleWords : Nat) : Nat :=
  HashDispatch.codeBudget layout.hash mulWords addWords sampleWords + 208 * layout.width + 80

variable [Zero F] [Mul F] [Add F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (zeroValid : layout.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (port : Interactive.Port w spec)

theorem time_bound {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler) {mulTime mulWords addTime addWords sampleTime : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound port .unit layout.hashInput.representation
      (code layout zeroValid mul add mulBuffers addBuffers reserve port sampler) (timeBudget layout mulTime addTime sampleTime) := by
  have coreRefines := HashDispatch.refines layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect
  have coreTime := HashDispatch.time_bound layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect
    mulBound addBound sampleBound
  have retainedTime := (Interactive.TimeBound.retain coreRefines coreTime (by decide) layout.scheme.config.representation
    layout.scheme.wordFits layout.hashInputFits).mono (Interactive.retain_time_unit_le _ _ _ _ _)
  have preparedTime := Interactive.TimeBound.compute (port := port) (cost := .unit) (prepare layout) _ (prepare_time layout)
  have finishedTime := Interactive.TimeBound.compute (port := port) (cost := .unit) (finish layout) _ (finish_time layout)
  have combined := preparedTime.seq (Interactive.Refines.compute port .unit (prepare layout))
    (retainedTime.seq (retained_refines layout zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect) finishedTime)
  apply combined.mono
  have := prepared_le layout
  have := layout.scalarOutput_le
  have := layout.hash.input_le
  have output : (Read.output layout.hash.hash.scheme).representation.encoding.words ≤ layout.width := layout.readOutput_le
  have := layout.core_widths
  have := layout.config_le
  unfold timeBudget
  omega

theorem code_bound (sampler : Interactive.Code w) {mulTime mulWords addTime addWords sampleWords : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (sampleBound : (sampler.lower port).descriptionWords ≤ sampleWords) :
    ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).descriptionWords ≤
      codeBudget layout mulWords addWords sampleWords := by
  have preparedBound := prepare_words layout
  have finishedBound := finish_words layout
  have coreBound := HashDispatch.code_bound layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler
    mulBound addBound sampleBound
  have retainedBound := Interactive.retain_descriptionWords_le port
    (HashDispatch.code layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler)
    (Interactive.savedBuffer port (HashDispatch.code layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler))
    layout.hash.input.representation.encoding.words (Read.output layout.scheme).representation.encoding.words
    layout.scheme.config.representation.encoding.words
  change ((retained layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).descriptionWords ≤ _ at retainedBound
  have form := composed_words port (prepare layout).code (finish layout).code
    (retained layout zeroValid mul add mulBuffers addBuffers reserve port sampler)
  change ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).descriptionWords = _ at form
  rw [form]
  have := prepared_le layout
  have := layout.scalarOutput_le
  have := layout.hash.input_le
  have := layout.readOutput_le
  have := layout.core_widths
  have := layout.config_le
  unfold codeBudget
  omega

theorem names (sampler : Interactive.Code w) {sampleSlots : Nat}
    (mulNames : NamesBound mul.program.code slots) (addNames : NamesBound add.program.code slots)
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    WordIO.NamesAccounted ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port)
      (max 5 (Fresh.nameBudget slots sampleSlots)) :=
  (WordIO.NamesAccounted.compute (prepare_names layout _)).seq
    ((Interactive.retain_names port
      (HashDispatch.names layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler mulNames addNames sampleNames) _ _ _).seq
      (WordIO.NamesAccounted.compute (finish_names layout _)))

theorem buffers (sampler : Interactive.Code w) {sampleSlots : Nat}
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).memBound ≤
      max 12 (Fresh.nameBudget slots sampleSlots + 4) := by
  have coreBound := HashDispatch.buffers layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler addNames sampleNames
  have retainedBound := Interactive.retain_buffers port
    (HashDispatch.code layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler)
    layout.hash.input.representation.encoding.words (Read.output layout.scheme).representation.encoding.words
    layout.scheme.config.representation.encoding.words
  have middle : ((retained layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).memBound ≤
      max 12 (Fresh.nameBudget slots sampleSlots + 4) := retainedBound.trans (by omega)
  exact max_le ((prepare_buffers layout).trans (by omega))
    (max_le middle ((finish_buffers layout).trans (by omega)))

theorem descriptionFits (sampler : Interactive.Code w) {sampleSlots : Nat}
    (sampleFits : (sampler.lower port).DescriptionFits)
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (sampleReserve : max slots sampleSlots + 4 < 2 ^ w) :
    ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).DescriptionFits := by
  have name : Interactive.savedBuffer port
      (HashDispatch.code layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler) < 2 ^ w := by
    have coreBound := HashDispatch.buffers layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler addNames sampleNames
    have := layout.scheme.wordFits
    unfold Interactive.savedBuffer
    unfold Fresh.nameBudget at coreBound
    omega
  have retainedFits := Interactive.retain_descriptionFits port
    (HashDispatch.code layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler)
    (Interactive.savedBuffer port (HashDispatch.code layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler))
    layout.hash.input.representation.encoding.words (Read.output layout.scheme).representation.encoding.words
    layout.scheme.config.representation.encoding.words layout.scheme.wordFits
    (HashDispatch.descriptionFits layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler sampleFits addNames sampleNames sampleReserve)
    name layout.hash.input.representation.fits layout.scheme.config.representation.fits layout.hashOutputFits
  exact .seq layout.scheme.wordFits (.compute (prepare layout).description_fits)
    (.seq layout.scheme.wordFits retainedFits (.compute (finish layout).description_fits))

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.HashComponent
