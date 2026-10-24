import Proofs.Runtime.Caliper.SchnorrAGMRead

/-! Derived time, stored code, and buffer bounds for the full read wrapper.
Its overhead is linear in the declared layout width, including metadata copies. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Read
open Caliper BoundedSource OracleComp OracleSpec Assembly
variable {w qH qS : Nat} {M F G I : Type} [Zero F] [Add F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : Layouts w M F G qH qS) (zeroValid : layout.scalar.valid 0)
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (slotsFit : slots < 2 ^ w)
    (port : Interactive.Port w spec)

def timeBudget (addTime sampleTime : Nat) : Nat := Cache.timeBudget layout addTime sampleTime + 100 * layout.width
def codeBudget (addWords sampleWords : Nat) : Nat := Cache.codeBudget layout addWords sampleWords + 400 * layout.width + 80

omit [Add F] [DecidableEq F] in
theorem core_sizes : (Cache.model layout).input.encoding.words ≤ 3 * layout.width ∧
    (Cache.model layout).output.encoding.words ≤ 3 * layout.width ∧
    layout.metadata.representation.encoding.words ≤ layout.width := by
  have packedSize : (Cache.model layout).input.encoding.words + layout.metadata.representation.encoding.words ≤ 3 * layout.width :=
    (sizes layout).2.1
  have returnedSize : (Cache.model layout).output.encoding.words + layout.metadata.representation.encoding.words ≤ 3 * layout.width :=
    (sizes layout).2.2.1
  have parts := components layout
  omega

theorem time_bound {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scalar.representation
      (fun _ => sampleSource) sampler) {addTime sampleTime : Nat}
    (addBound : ∀ value, add.program.time value ≤ addTime)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound port .unit (input layout).representation
      (code layout zeroValid add addBuffers slotsFit port sampler) (timeBudget layout addTime sampleTime) := by
  have packedBound := Interactive.TimeBound.compute (port := port) (cost := .unit) (pack layout zeroValid)
    (8 * (packed layout).encoding.words) (fun _ => by
      have bound := code_time_unit_le (packOperands layout zeroValid)
      rw [packOperands_length] at bound
      exact bound)
  have cached := (Cache.time_bound layout zeroValid add addBuffers slotsFit port sampleCorrect addBound sampleBound).retain
    (Cache.refines layout zeroValid add addBuffers slotsFit port sampleCorrect) (by decide)
    layout.metadata.representation layout.wordFits (packed layout).fits
  have retainedBound := cached.mono (Interactive.retain_time_unit_le _ _ _ _ _)
  have finished := Interactive.TimeBound.compute (port := port) (cost := .unit) (finish layout)
    (8 * (output layout).representation.encoding.words) (fun _ => by
      have bound := code_time_unit_le (finishOperands layout)
      rw [finishOperands_length] at bound
      exact bound)
  have combined := packedBound.seq (Interactive.Refines.compute port .unit (pack layout zeroValid))
    (retainedBound.seq (retained_refines layout zeroValid add addBuffers slotsFit port sampleCorrect) finished)
  apply combined.mono
  have frames := sizes layout
  have core := core_sizes layout
  unfold timeBudget
  omega

theorem code_bound (sampler : Interactive.Code w) {addWords sampleWords : Nat}
    (addBound : descriptionWords add.program.code ≤ addWords)
    (sampleBound : (sampler.lower port).descriptionWords ≤ sampleWords) :
    ((code layout zeroValid add addBuffers slotsFit port sampler).lower port).descriptionWords ≤ codeBudget layout addWords sampleWords := by
  have packedBound := code_descriptionWords_le (packOperands layout zeroValid)
  rw [packOperands_length] at packedBound
  have finished := code_descriptionWords_le (finishOperands layout)
  rw [finishOperands_length] at finished
  have cached := Cache.code_bound layout zeroValid add addBuffers slotsFit port sampler addBound sampleBound
  have held := Interactive.retain_descriptionWords_le port (Cache.code layout zeroValid add addBuffers slotsFit port sampler)
    (Interactive.savedBuffer port (Cache.code layout zeroValid add addBuffers slotsFit port sampler))
    (Cache.model layout).input.encoding.words (Cache.model layout).output.encoding.words layout.metadata.representation.encoding.words
  change descriptionWords (pack layout zeroValid).code ≤ _ at packedBound
  change descriptionWords (finish layout).code ≤ _ at finished
  change ((retained layout zeroValid add addBuffers slotsFit port sampler).lower port).descriptionWords ≤ _ at held
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  have frames := sizes layout
  have core := core_sizes layout
  unfold codeBudget
  omega

theorem names (sampler : Interactive.Code w) {sampleSlots : Nat}
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    WordIO.NamesAccounted ((code layout zeroValid add addBuffers slotsFit port sampler).lower port)
      (max 5 (Fresh.nameBudget slots sampleSlots)) :=
  (WordIO.NamesAccounted.compute (code_namesAccounted _ _ (packOperands_sources layout zeroValid))).seq
    ((Interactive.retain_names port (Cache.names layout zeroValid add addBuffers slotsFit port sampler addNames sampleNames) _ _ _).seq
      (WordIO.NamesAccounted.compute (code_namesAccounted _ _ (finishOperands_sources layout))))

theorem buffers (sampler : Interactive.Code w) {sampleSlots : Nat}
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    ((code layout zeroValid add addBuffers slotsFit port sampler).lower port).memBound ≤
      max 10 (Fresh.nameBudget slots sampleSlots + 2) := by
  have packedBound := (code_names _ 1 (packOperands_sources layout zeroValid)).2
  have finished := (code_names _ 1 (finishOperands_sources layout)).2
  have cached := cache_buffers layout zeroValid add addBuffers slotsFit port sampler addNames sampleNames
  have held := Interactive.retain_buffers port (Cache.code layout zeroValid add addBuffers slotsFit port sampler)
    (Cache.model layout).input.encoding.words (Cache.model layout).output.encoding.words layout.metadata.representation.encoding.words
  change (pack layout zeroValid).code.memBound ≤ 2 at packedBound
  change (finish layout).code.memBound ≤ 2 at finished
  change ((retained layout zeroValid add addBuffers slotsFit port sampler).lower port).memBound ≤ _ at held
  change max (pack layout zeroValid).code.memBound
    (max ((retained layout zeroValid add addBuffers slotsFit port sampler).lower port).memBound (finish layout).code.memBound) ≤ _
  omega

theorem descriptionFits (sampler : Interactive.Code w) {sampleSlots : Nat}
    (sampleFits : (sampler.lower port).DescriptionFits)
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (reserve : max slots sampleSlots + 2 < 2 ^ w) :
    ((code layout zeroValid add addBuffers slotsFit port sampler).lower port).DescriptionFits := by
  have cached := Cache.descriptionFits layout zeroValid add addBuffers slotsFit port sampler sampleFits addNames sampleNames reserve
  have held := Interactive.retain_descriptionFits port (Cache.code layout zeroValid add addBuffers slotsFit port sampler)
    (Interactive.savedBuffer port (Cache.code layout zeroValid add addBuffers slotsFit port sampler))
    (Cache.model layout).input.encoding.words (Cache.model layout).output.encoding.words layout.metadata.representation.encoding.words
    layout.wordFits cached (by
      have bounded := cache_buffers layout zeroValid add addBuffers slotsFit port sampler addNames sampleNames
      have hw := layout.wordFits
      unfold Fresh.nameBudget at bounded
      change max 2 ((Cache.code layout zeroValid add addBuffers slotsFit port sampler).lower port).memBound < _
      omega) (Cache.model layout).input.fits layout.metadata.representation.fits (returned layout).fits
  exact .seq layout.wordFits (.compute (pack layout zeroValid).description_fits)
    (.seq layout.wordFits held (.compute (finish layout).description_fits))

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Read
