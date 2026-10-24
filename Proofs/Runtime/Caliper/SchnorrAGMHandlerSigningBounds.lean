import Proofs.Runtime.Caliper.SchnorrAGMHandlerSigning

/-! Common-store signing overhead charges argument construction, configuration
retention and reply restoration in addition to the complete signing-core budget. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.SigningComponent
open Caliper BoundedSource OracleComp OracleSpec
private theorem composed_words {w : Nat} {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    (preparation wrapping : Stmt w) (body : Interactive.Code w) :
    ((Interactive.Code.seq (.compute preparation) (.seq body (.compute wrapping))).lower port).descriptionWords =
      descriptionWords preparation + (body.lower port).descriptionWords + descriptionWords wrapping + 4 := by
  simp only [Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega

variable {w qH qS randomBound : Nat} {M F G I : Type}
    (layout : Handler.Layouts w M F G qH qS randomBound)
theorem prepared_le : layout.signingPrepared.encoding.words ≤ 2 * layout.width := by
  change layout.signing.input.representation.encoding.words + layout.scheme.config.representation.encoding.words ≤ _
  have := layout.signing.input_le; have := layout.core_widths; have := layout.config_le; omega
def timeBudget (scaleTime subTime negateTime sampleTime : Nat) : Nat :=
  SigningDispatch.timeBudget layout.signing scaleTime subTime negateTime sampleTime + 64 * layout.width
def codeBudget (scaleWords subWords negateWords sampleWords : Nat) : Nat :=
  SigningDispatch.codeBudget layout.signing scaleWords subWords negateWords sampleWords + 208 * layout.width + 80

variable [Zero F] [SMul F G] [Sub G] [Neg F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.arithmetic.arithmetic.scaleArgs layout.scheme.point (fun args => args.1 • args.2))
    (sub : Implementation .unit layout.arithmetic.arithmetic.points layout.scheme.point (fun args => args.1 - args.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (port : Interactive.Port w spec)

theorem time_bound {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler) {scaleTime scaleWords subTime subWords negateTime negateWords sampleTime : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (negateBound : negate.BoundedBy negateTime negateWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound port .unit layout.signingInput.representation
      (code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler)
      (timeBudget layout scaleTime subTime negateTime sampleTime) := by
  have coreRefines := SigningDispatch.refines layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampleCorrect
  have coreTime := SigningDispatch.time_bound layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampleCorrect
    scaleBound subBound negateBound sampleBound
  have retainedTime := (Interactive.TimeBound.retain coreRefines coreTime (by decide) layout.scheme.config.representation
    layout.scheme.wordFits layout.signingInputFits).mono (Interactive.retain_time_unit_le _ _ _ _ _)
  have preparedTime := Interactive.TimeBound.compute (port := port) (cost := .unit) (prepare layout) _ (prepare_time layout)
  have finishedTime := Interactive.TimeBound.compute (port := port) (cost := .unit) (finish layout) _ (finish_time layout)
  have combined := preparedTime.seq (Interactive.Refines.compute port .unit (prepare layout))
    (retainedTime.seq
      (retained_refines layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampleCorrect) finishedTime)
  apply combined.mono
  have := prepared_le layout
  have := layout.scalarOutput_le
  have := layout.signing.input_le
  have := layout.signing.output_le
  have := layout.core_widths
  have := layout.config_le
  unfold timeBudget
  omega

theorem code_bound (sampler : Interactive.Code w) {scaleTime scaleWords subTime subWords negateTime negateWords sampleWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (negateBound : negate.BoundedBy negateTime negateWords)
    (sampleBound : (sampler.lower port).descriptionWords ≤ sampleWords) :
    ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).descriptionWords ≤
      codeBudget layout scaleWords subWords negateWords sampleWords := by
  have preparedBound := prepare_words layout
  have finishedBound := finish_words layout
  have coreBound := SigningDispatch.code_bound layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler
    scaleBound subBound negateBound sampleBound
  have retainedBound := Interactive.retain_descriptionWords_le port
    (SigningDispatch.code layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler)
    (Interactive.savedBuffer port (SigningDispatch.code layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler))
    layout.signing.input.representation.encoding.words layout.signing.output.representation.encoding.words
    layout.scheme.config.representation.encoding.words
  change ((retained layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).descriptionWords ≤ _ at retainedBound
  have form := composed_words port (prepare layout).code (finish layout).code
    (retained layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler)
  change ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).descriptionWords = _ at form
  rw [form]
  have := prepared_le layout
  have := layout.scalarOutput_le
  have := layout.signing.input_le
  have := layout.signing.output_le
  have := layout.core_widths
  have := layout.config_le
  unfold codeBudget
  omega

theorem names (sampler : Interactive.Code w) {primitiveNames sampleSlots : Nat}
    (scaleNames : NamesAccounted scale.program.code primitiveNames) (subNames : NamesAccounted sub.program.code primitiveNames)
    (negateNames : NamesAccounted negate.program.code primitiveNames)
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    WordIO.NamesAccounted ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port)
      (Signing.Sampling.nameBudget primitiveNames sampleSlots) :=
  (WordIO.NamesAccounted.compute (prepare_names layout _)).seq
    ((Interactive.retain_names port
      (SigningDispatch.names layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler
        scaleNames subNames negateNames sampleNames) _ _ _).seq
      (WordIO.NamesAccounted.compute (finish_names layout _)))

theorem buffers (sampler : Interactive.Code w) {sampleSlots : Nat}
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).memBound ≤
      max 10 (max (slots + 4) (sampleSlots + 3)) := by
  have coreBound := SigningDispatch.buffers layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler sampleNames
  have retainedBound := Interactive.retain_buffers port
    (SigningDispatch.code layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler)
    layout.signing.input.representation.encoding.words layout.signing.output.representation.encoding.words
    layout.scheme.config.representation.encoding.words
  have middle : ((retained layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).memBound ≤
      max 10 (max (slots + 4) (sampleSlots + 3)) := retainedBound.trans (by omega)
  exact max_le ((prepare_buffers layout).trans (by omega))
    (max_le middle ((finish_buffers layout).trans (by omega)))

theorem descriptionFits (sampler : Interactive.Code w) {sampleSlots : Nat}
    (sampleFits : (sampler.lower port).DescriptionFits)
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) (sampleReserve : sampleSlots + 2 < 2 ^ w) :
    ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).DescriptionFits := by
  have name : Interactive.savedBuffer port
      (SigningDispatch.code layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler) < 2 ^ w := by
    have coreBound := SigningDispatch.buffers layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler sampleNames
    have := layout.scheme.wordFits
    unfold Interactive.savedBuffer
    omega
  have retainedFits := Interactive.retain_descriptionFits port
    (SigningDispatch.code layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler)
    (Interactive.savedBuffer port (SigningDispatch.code layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler))
    layout.signing.input.representation.encoding.words layout.signing.output.representation.encoding.words
    layout.scheme.config.representation.encoding.words layout.scheme.wordFits
    (SigningDispatch.descriptionFits layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler
      sampleFits sampleNames sampleReserve)
    name layout.signing.input.representation.fits layout.scheme.config.representation.fits layout.signingOutputFits
  exact .seq layout.scheme.wordFits (.compute (prepare layout).description_fits)
    (.seq layout.scheme.wordFits retainedFits (.compute (finish layout).description_fits))

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.SigningComponent
