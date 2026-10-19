import Signatures.Runtime.Caliper.SchnorrAGMFresh

/-! Complete resource bounds for the stateful fresh routine, derived from the
scalar sampler and addition implementation. All retained explanation words,
constant zero words, code and intermediate buffers are included. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Fresh
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G I : Type} [Zero F] [Add F] [DecidableEq F]
    {spec : OracleSpec I} (layout : Layouts w M F G qH qS)
    (zeroValid : layout.scalar.valid 0)
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (slotsFit : slots < 2 ^ w)
    (port : Interactive.Port w spec)

def timeBudget (addTime sampleTime : Nat) : Nat :=
  sampleTime + arithmeticTime layout addTime + 32 * layout.scalar.representation.encoding.words + 12
def codeBudget (addWords sampleWords : Nat) : Nat :=
  sampleWords + arithmeticWords layout addWords + 104 * layout.scalar.representation.encoding.words + 82
def nameBudget (addSlots sampleSlots : Nat) : Nat := max 6 (max (addSlots + 1) (sampleSlots + 1))

theorem time_bound {source : OracleComp spec layout.scalar.Value} {sampler : Interactive.Code w}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scalar.representation
      (fun _ => source) sampler) {addTime sampleTime : Nat}
    (addBound : ∀ value, add.program.time value ≤ addTime)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound port .unit (Cache.saved layout).representation
      (code layout zeroValid add addBuffers slotsFit port sampler) (timeBudget layout addTime sampleTime) := by
  have retained := sampleBound.retain sampleCorrect (by decide) (Cache.saved layout).representation layout.wordFits
    (by change 0 + _ < _; simpa using (Cache.saved layout).representation.fits)
  have viewed := retained.viewInput (Cache.saved layout).representation (fun state => (⟨(), trivial⟩, state)) (fun _ => rfl)
  have sampled := viewed.mono (Interactive.retain_time_unit_le _ 0 _ _ _)
  have combined := sampled.seq (sample_refines layout port sampleCorrect)
    (Interactive.TimeBound.compute (port := port) (cost := .unit)
      (arithmetic layout zeroValid add addBuffers slotsFit) (arithmeticTime layout addTime)
      (arithmetic_time layout zeroValid add addBuffers slotsFit addBound))
  apply combined.mono
  change sampleTime + 8 * 0 + 8 * layout.scalar.representation.encoding.words +
    12 * ((layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words) + 1) + _ ≤ _
  unfold timeBudget
  omega

theorem code_bound (sampler : Interactive.Code w) {addWords sampleWords : Nat}
    (addBound : descriptionWords add.program.code ≤ addWords)
    (sampleBound : (sampler.lower port).descriptionWords ≤ sampleWords) :
    ((code layout zeroValid add addBuffers slotsFit port sampler).lower port).descriptionWords ≤
      codeBudget layout addWords sampleWords := by
  have retained := Interactive.retain_descriptionWords_le port sampler (Interactive.savedBuffer port sampler) 0
    layout.scalar.representation.encoding.words (Cache.saved layout).representation.encoding.words
  have computed := arithmetic_words layout zeroValid add addBuffers slotsFit addBound
  change ((sample layout port sampler).lower port).descriptionWords ≤ (sampler.lower port).descriptionWords +
    26 * 0 + 26 * layout.scalar.representation.encoding.words +
      39 * ((layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words) + 1) + 41 at retained
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names (sampler : Interactive.Code w) {sampleSlots : Nat}
    (addNames : NamesBound add.program.code slots)
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    WordIO.NamesBound ((code layout zeroValid add addBuffers slotsFit port sampler).lower port)
      (nameBudget slots sampleSlots) := by
  have prepared := Retain.prepare_names (w := w) (Interactive.savedBuffer port sampler) 0
    (Cache.saved layout).representation.encoding.words
  have restored := Retain.finish_names (w := w) (Interactive.savedBuffer port sampler)
    layout.scalar.representation.encoding.words (Cache.saved layout).representation.encoding.words
  have savedBuffers := Interactive.retain_buffers port sampler 0 layout.scalar.representation.encoding.words
    (Cache.saved layout).representation.encoding.words
  have computed := arithmetic_names layout zeroValid add addBuffers slotsFit addNames
  rcases sampleNames with ⟨sampleRegisters, sampleBuffers⟩
  constructor
  · simp only [code, sample, Interactive.retain, Interactive.Code.lower, WordIO.Code.registerSlots]
    have := computed.registers
    unfold nameBudget
    omega
  · change max ((sample layout port sampler).lower port).memBound
      (arithmetic layout zeroValid add addBuffers slotsFit).code.memBound ≤ _
    change ((sample layout port sampler).lower port).memBound ≤ _ at savedBuffers
    have := computed.buffers
    unfold nameBudget
    omega

theorem descriptionFits (sampler : Interactive.Code w) (sampleFits : (sampler.lower port).DescriptionFits)
    {sampleSlots : Nat} (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (sampleSlotsFit : sampleSlots < 2 ^ w) :
    ((code layout zeroValid add addBuffers slotsFit port sampler).lower port).DescriptionFits := by
  have saved := Interactive.retain_descriptionFits port sampler (Interactive.savedBuffer port sampler) 0
    layout.scalar.representation.encoding.words (Cache.saved layout).representation.encoding.words layout.wordFits sampleFits
    (by have := sampleNames.buffers; have := layout.wordFits; change max 2 (sampler.lower port).memBound < _; omega)
    (by positivity) (Cache.saved layout).representation.fits (input layout).fits
  exact .seq layout.wordFits saved (.compute (arithmetic layout zeroValid add addBuffers slotsFit).description_fits)

theorem resources {source : OracleComp spec layout.scalar.Value} {sampler : Interactive.Code w}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scalar.representation
      (fun _ => source) sampler) {addTime addWords sampleTime sampleWords sampleSlots : Nat}
    (addBound : add.BoundedBy addTime addWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime)
    (sampleStored : (sampler.lower port).descriptionWords ≤ sampleWords)
    (addNames : NamesBound add.program.code slots)
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (tape : RandomTape w) (value : (Cache.saved layout).Value) (before : State w)
    (holds : (Cache.saved layout).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout zeroValid add addBuffers slotsFit port sampler).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout addTime sampleTime ∧
      ∃ answer ∈ support (denote layout source value), (Cache.model layout).freshOutput.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit tape ((code layout zeroValid add addBuffers slotsFit port sampler).lower port)
            before finished.state finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            RegisterBound between (max registers ((code layout zeroValid add addBuffers slotsFit port sampler).lower port).registerSlots) ∧
            between.SupportBound (max buffers ((code layout zeroValid add addBuffers slotsFit port sampler).lower port).memBound) ∧ between.WellFormed ∧
            (((code layout zeroValid add addBuffers slotsFit port sampler).lower port).staticWords registers buffers : Int) +
              between.liveMem (max buffers ((code layout zeroValid add addBuffers slotsFit port sampler).lower port).memBound) ≤
                codeBudget layout addWords sampleWords + 4 * nameBudget slots sampleSlots + registers + 3 * buffers +
                  before.liveMem buffers + timeBudget layout addTime sampleTime :=
  (refines layout zeroValid add addBuffers slotsFit port sampleCorrect).resources
    (time_bound layout zeroValid add addBuffers slotsFit port sampleCorrect addBound.time_le sampleBound)
    (code_bound layout zeroValid add addBuffers slotsFit port sampler addBound.code_le sampleStored)
    (names layout zeroValid add addBuffers slotsFit port sampler addNames sampleNames)
    tape value before holds registers buffers initialRegisters initialBuffers finished reached

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Fresh
