import Proofs.Runtime.Caliper.SchnorrAGMHashDispatch

/-! All-shape hash bounds charge the executed length test, selector, branch
payload copies, accepted-input routing and deterministic malformed rejection. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.HashDispatch
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
    {spec : OracleSpec I} (layout : Layouts w M F G qH qS) (zeroValid : layout.hash.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (port : Interactive.Port w spec)

def timeBudget (mulTime addTime sampleTime : Nat) : Nat := Hash.timeBudget layout.hash mulTime addTime sampleTime + 100 * layout.width + 100
def codeBudget (mulWords addWords sampleWords : Nat) : Nat := Hash.codeBudget layout.hash mulWords addWords sampleWords + 400 * layout.width + 600

theorem accepted_time {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.hash.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.hash.scheme.scalar.representation
      (fun _ => sampleSource) sampler) {mulTime mulWords addTime addWords sampleTime : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound port .unit layout.yes.representation
      (accepted layout zeroValid mul add mulBuffers addBuffers reserve port sampler)
      (8 * layout.hash.input.representation.encoding.words + Hash.timeBudget layout.hash mulTime addTime sampleTime) := by
  have packed := Interactive.TimeBound.compute (port := port) (cost := .unit) (accept layout) _ (accept_time layout)
  have hashed := Hash.time_bound layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect mulBound addBound sampleBound
  exact packed.seq (Interactive.Refines.compute port .unit (accept layout)) hashed

theorem dispatch_time {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.hash.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.hash.scheme.scalar.representation
      (fun _ => sampleSource) sampler) {mulTime mulWords addTime addWords sampleTime : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound port .unit layout.selected.representation
      (dispatch layout zeroValid mul add mulBuffers addBuffers reserve port sampler)
      (Interactive.dispatchTime (w := w) .unit layout.yes.representation.encoding.words layout.no.representation.encoding.words
        (8 * layout.hash.input.representation.encoding.words + Hash.timeBudget layout.hash mulTime addTime sampleTime)
        (8 * (Read.output layout.hash.scheme).representation.encoding.words)) := by
  have acceptedBound := accepted_time layout zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect mulBound addBound sampleBound
  have rejectedBound := Interactive.TimeBound.compute (port := port) (cost := .unit) (rejected layout zeroValid)
    (8 * (Read.output layout.hash.scheme).representation.encoding.words)
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
  have selected := Interactive.TimeBound.compute (port := port) (cost := .unit) (selector layout).program _ (selector_bounded layout).time_le
  have branches := dispatch_time layout zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect mulBound addBound sampleBound
  have combined := selected.seq (Interactive.Refines.compute port .unit (selector layout).program) branches
  apply combined.mono
  rw [Interactive.dispatchTime_unit]
  have inputSize := layout.input_le
  have hashSize := layout.hash.sizes
  have outputSize := Read.sizes layout.hash.scheme
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
  have selected := (selector_bounded layout).code_le
  have packed := accept_words layout
  have hashed := Hash.code_bound layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler mulBound addBound sampleBound
  have rejected := reject_words layout zeroValid
  have form := composed_words port (selector layout).program.code (accept layout).code (HashDispatch.rejected layout zeroValid).code
    (Hash.code layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler)
    layout.yes.representation.encoding.words layout.no.representation.encoding.words
  change ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).descriptionWords =
    descriptionWords (selector layout).program.code + descriptionWords (accept layout).code +
      ((Hash.code layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).descriptionWords +
        descriptionWords (reject layout zeroValid).code + 26 * layout.input.representation.encoding.words +
          26 * layout.input.representation.encoding.words + 45 at form
  rw [form]
  have inputSize := layout.input_le
  have hashSize := layout.hash.sizes
  have outputSize := Read.sizes layout.hash.scheme
  have widths := layout.hash.width_eq
  have parts := layout.parts
  unfold codeBudget
  omega

theorem names (sampler : Interactive.Code w) {sampleSlots : Nat}
    (mulNames : NamesBound mul.program.code slots) (addNames : NamesBound add.program.code slots)
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    WordIO.NamesAccounted ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port)
      (max 5 (Fresh.nameBudget slots sampleSlots)) := by
  have selected := (selector_names layout).mono (Nat.le_max_left 5 (Fresh.nameBudget slots sampleSlots))
  have acceptedBound := (WordIO.NamesAccounted.compute (accept_names layout (max 5 (Fresh.nameBudget slots sampleSlots)))).seq
    (Hash.names layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler mulNames addNames sampleNames)
  exact (WordIO.NamesAccounted.compute selected).seq (Interactive.dispatch_names port
    («left» := accepted layout zeroValid mul add mulBuffers addBuffers reserve port sampler)
    («right» := .compute (rejected layout zeroValid).code) acceptedBound
    (WordIO.NamesAccounted.compute (reject_names layout zeroValid (max 5 (Fresh.nameBudget slots sampleSlots)))) _ _)

theorem buffers (sampler : Interactive.Code w) {sampleSlots : Nat}
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).memBound ≤
      max 11 (Fresh.nameBudget slots sampleSlots + 3) := by
  have selected := selector_buffers layout
  have packed := accept_buffers layout
  have hashed := Hash.buffers layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler addNames sampleNames
  have rejected := reject_buffers layout zeroValid
  have branches := Interactive.dispatch_buffers port (accepted layout zeroValid mul add mulBuffers addBuffers reserve port sampler)
    (.compute (HashDispatch.rejected layout zeroValid).code) layout.yes.representation.encoding.words layout.no.representation.encoding.words
  change ((dispatch layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).memBound ≤
    max 2 (max (max (accept layout).code.memBound ((Hash.code layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).memBound)
      (reject layout zeroValid).code.memBound) at branches
  change max (selector layout).program.code.memBound ((dispatch layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).memBound ≤ _
  omega

theorem descriptionFits (sampler : Interactive.Code w) {sampleSlots : Nat}
    (sampleFits : (sampler.lower port).DescriptionFits)
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (sampleReserve : max slots sampleSlots + 4 < 2 ^ w) :
    ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).DescriptionFits :=
  .seq layout.hash.scheme.wordFits (.compute (selector layout).program.description_fits)
    (Interactive.dispatch_descriptionFits port _ _ _ _ layout.hash.scheme.wordFits
      (.seq layout.hash.scheme.wordFits (.compute (accept layout).description_fits)
        (Hash.descriptionFits layout.hash zeroValid mul add mulBuffers addBuffers reserve port sampler sampleFits addNames sampleNames sampleReserve))
      (.compute (rejected layout zeroValid).description_fits) layout.yes.representation.fits layout.no.representation.fits)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.HashDispatch
