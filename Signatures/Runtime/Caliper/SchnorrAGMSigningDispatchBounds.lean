import Signatures.Runtime.Caliper.SchnorrAGMSigningDispatch

/-! All-shape signing bounds charge the executed length test, selector, branch
payload copies, accepted-input routing, reply encoding and deterministic malformed rejection. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.SigningDispatch
open Caliper BoundedSource OracleComp OracleSpec
private theorem composed_words {w : Nat} {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    (selection preparation wrapping rejection : Stmt w) (body : Interactive.Code w) (yesWords noWords : Nat) :
    ((Interactive.Code.seq (.compute selection)
      (Interactive.dispatch (.seq (.compute preparation) (.seq body (.compute wrapping))) (.compute rejection) yesWords noWords)).lower port).descriptionWords =
      descriptionWords selection + descriptionWords preparation + (body.lower port).descriptionWords +
        descriptionWords wrapping + descriptionWords rejection + 26 * yesWords + 26 * noWords + 47 := by
  change (WordIO.Code.seq (.compute selection)
    ((Interactive.dispatch (.seq (.compute preparation) (.seq body (.compute wrapping))) (.compute rejection) yesWords noWords).lower port)).descriptionWords = _
  rw [WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  rw [Interactive.dispatch_descriptionWords]
  simp only [Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega

variable {w qH qS : Nat} {M F G I : Type} [Zero F] [SMul F G] [Sub G] [Neg F]
    [DecidableEq M] [DecidableEq G] {spec : OracleSpec I}
    (layout : Layouts w M F G qH qS) (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.signing.signing.arithmetic.scaleArgs layout.scheme.point (fun args => args.1 • args.2))
    (sub : Implementation .unit layout.signing.signing.arithmetic.points layout.scheme.point (fun args => args.1 - args.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (port : Interactive.Port w spec)

def timeBudget (scaleTime subTime negateTime sampleTime : Nat) : Nat := Signing.Sampling.timeBudget layout.signing scaleTime subTime negateTime sampleTime + 128 * layout.width + 100
def codeBudget (scaleWords subWords negateWords sampleWords : Nat) : Nat := Signing.Sampling.codeBudget layout.signing scaleWords subWords negateWords sampleWords + 512 * layout.width + 512

theorem accepted_time {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler) {scaleTime scaleWords subTime subWords negateTime negateWords sampleTime : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (negateBound : negate.BoundedBy negateTime negateWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound port .unit layout.yes.representation
      (accepted layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler)
      (16 * layout.width + (Signing.Sampling.timeBudget layout.signing scaleTime subTime negateTime sampleTime + 8 * layout.output.representation.encoding.words)) := by
  have packed := Interactive.TimeBound.compute (port := port) (cost := .unit) (accept layout) _ (accept_time layout)
  have sampled := Signing.Sampling.time_bound layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampleCorrect scaleBound subBound negateBound sampleBound
  have wrapped := Interactive.TimeBound.compute (port := port) (cost := .unit) (wrap layout) _ (wrap_time layout)
  have signed := sampled.seq
    (Signing.Sampling.refines layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampleCorrect) wrapped
  exact packed.seq (Interactive.Refines.compute port .unit (accept layout)) signed

theorem dispatch_time {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler) {scaleTime scaleWords subTime subWords negateTime negateWords sampleTime : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (negateBound : negate.BoundedBy negateTime negateWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound port .unit layout.selected.representation
      (dispatch layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler)
      (Interactive.dispatchTime (w := w) .unit layout.yes.representation.encoding.words layout.no.representation.encoding.words
        (16 * layout.width + (Signing.Sampling.timeBudget layout.signing scaleTime subTime negateTime sampleTime + 8 * layout.output.representation.encoding.words))
        (8 * layout.output.representation.encoding.words)) := by
  have acceptedBound := accepted_time layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampleCorrect scaleBound subBound negateBound sampleBound
  have rejectedBound := Interactive.TimeBound.compute (port := port) (cost := .unit) (rejected layout zeroValid)
    (8 * layout.output.representation.encoding.words)
    (fun value => reject_time layout zeroValid ⟨value.val, value.property.1⟩)
  exact (Interactive.TimeBound.dispatch layout.yes.representation layout.no.representation acceptedBound rejectedBound
    (width_pos layout.scheme.wordFits) layout.selected.representation.fits).viewInput
      layout.selected.representation (sumView layout.yes layout.no) (fun _ => rfl)

theorem time_bound {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler) {scaleTime scaleWords subTime subWords negateTime negateWords sampleTime : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (negateBound : negate.BoundedBy negateTime negateWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound port .unit layout.input.representation
      (code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler) (timeBudget layout scaleTime subTime negateTime sampleTime) := by
  have selected := Interactive.TimeBound.compute (port := port) (cost := .unit) (selector layout).program _ (selector_bounded layout).time_le
  have branches := dispatch_time layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampleCorrect scaleBound subBound negateBound sampleBound
  have combined := selected.seq (Interactive.Refines.compute port .unit (selector layout).program) branches
  apply combined.mono
  rw [Interactive.dispatchTime_unit]
  have inputSize := layout.input_le
  have outputSize := layout.output_le
  change _ + (2 + max (8 * layout.input.representation.encoding.words + _) (8 * layout.input.representation.encoding.words + _)) ≤ _
  unfold timeBudget
  omega

theorem code_bound (sampler : Interactive.Code w) {scaleTime scaleWords subTime subWords negateTime negateWords sampleWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (negateBound : negate.BoundedBy negateTime negateWords)
    (sampleBound : (sampler.lower port).descriptionWords ≤ sampleWords) :
    ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).descriptionWords ≤
      codeBudget layout scaleWords subWords negateWords sampleWords := by
  have selected := (selector_bounded layout).code_le
  have packed := accept_words layout
  have sampled := Signing.Sampling.code_bound layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler scaleBound subBound negateBound sampleBound
  have wrapped := wrap_words layout
  have rejected := reject_words layout zeroValid
  have form := composed_words port (selector layout).program.code (accept layout).code (wrap layout).code (SigningDispatch.rejected layout zeroValid).code
    (Signing.Sampling.code layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler)
    layout.yes.representation.encoding.words layout.no.representation.encoding.words
  change ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).descriptionWords =
    descriptionWords (selector layout).program.code + descriptionWords (accept layout).code +
      ((Signing.Sampling.code layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).descriptionWords +
        descriptionWords (wrap layout).code + descriptionWords (reject layout zeroValid).code + 26 * layout.input.representation.encoding.words +
          26 * layout.input.representation.encoding.words + 47 at form
  rw [form]
  have inputSize := layout.input_le
  have outputSize := layout.output_le
  unfold codeBudget
  omega

theorem names (sampler : Interactive.Code w) {primitiveNames sampleSlots : Nat}
    (scaleNames : NamesAccounted scale.program.code primitiveNames) (subNames : NamesAccounted sub.program.code primitiveNames)
    (negateNames : NamesAccounted negate.program.code primitiveNames)
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    WordIO.NamesAccounted ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port)
      (Signing.Sampling.nameBudget primitiveNames sampleSlots) := by
  have selected : NamesAccounted (selector layout).program.code (Signing.Sampling.nameBudget primitiveNames sampleSlots) :=
    (selector_names layout).mono (Nat.le_max_left 5 _)
  have signed := Signing.Sampling.names layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler
    scaleNames subNames negateNames sampleNames
  have acceptedBound := (WordIO.NamesAccounted.compute (accept_names layout (Signing.Sampling.nameBudget primitiveNames sampleSlots))).seq
    (signed.seq (WordIO.NamesAccounted.compute (wrap_names layout (Signing.Sampling.nameBudget primitiveNames sampleSlots))))
  exact (WordIO.NamesAccounted.compute selected).seq (Interactive.dispatch_names port
    («left» := accepted layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler)
    («right» := .compute (rejected layout zeroValid).code) acceptedBound
    (WordIO.NamesAccounted.compute (reject_names layout zeroValid (Signing.Sampling.nameBudget primitiveNames sampleSlots))) _ _)

theorem descriptionFits (sampler : Interactive.Code w) (sampleFits : (sampler.lower port).DescriptionFits)
    {sampleSlots : Nat} (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (sampleReserve : sampleSlots + 2 < 2 ^ w) :
    ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).DescriptionFits :=
  .seq layout.scheme.wordFits (.compute (selector layout).program.description_fits)
    (Interactive.dispatch_descriptionFits port _ _ _ _ layout.scheme.wordFits
      (.seq layout.scheme.wordFits (.compute (accept layout).description_fits)
        (.seq layout.scheme.wordFits
          (Signing.Sampling.descriptionFits layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler
            sampleFits sampleNames sampleReserve) (.compute (wrap layout).description_fits)))
      (.compute (rejected layout zeroValid).description_fits) layout.yes.representation.fits layout.no.representation.fits)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.SigningDispatch
