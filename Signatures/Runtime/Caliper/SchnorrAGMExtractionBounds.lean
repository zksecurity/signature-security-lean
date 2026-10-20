import Signatures.Runtime.Caliper.SchnorrAGMExtraction
import Signatures.Runtime.Caliper.SchnorrAGMExtractionEntryBounds

/-! Costs and descriptor acceptance for the complete final-forgery code.
Every retained scalar, state copy and arithmetic branch contributes to the
derived bounds; only primitive budgets and name extents are supplied. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Extraction
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G : Type} (layout : HashDispatch.Layouts w M F G qH qS)

def timeBudget (mulTime addTime subTime divTime sampleTime : Nat) : Nat :=
  ExtractionEntry.timeBudget layout mulTime addTime sampleTime + ExtractionArithmetic.timeBudget layout.hash.scheme addTime subTime divTime + 100 * layout.width
def codeBudget (mulWords addWords subWords divWords sampleWords : Nat) : Nat :=
  ExtractionEntry.codeBudget layout mulWords addWords sampleWords + ExtractionArithmetic.codeBudget layout.hash.scheme addWords subWords divWords + 400 * layout.width + 100
def nameBudget (slots sampleSlots : Nat) : Nat := max 5 (Fresh.nameBudget slots sampleSlots)

variable [DecidableEq M] [DecidableEq G]
theorem widths :
    layout.input.representation.encoding.words ≤ layout.width ∧
    (EntryRead.output layout.hash.scheme).representation.encoding.words ≤ layout.width ∧
    layout.hash.scheme.scalar.representation.encoding.words ≤ layout.width ∧ layout.hash.scheme.width ≤ layout.width := by
  have entry := EntryRead.output_size layout.hash.scheme
  have scalar := (ExtractionArithmetic.sizes layout.hash.scheme).2
  have widths := layout.hash.width_eq
  have parts := layout.parts
  exact ⟨layout.input_le, by omega, by omega, by omega⟩

variable [Zero F] [Mul F] [Add F] [Sub F] [Div F] [DecidableEq F]
    (zeroValid : layout.hash.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 + value.2))
    (sub : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 - value.2))
    (divide : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 / value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (divBuffers : divide.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)
    {mulTime mulWords addTime addWords subTime subWords divTime divWords : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords) (subBound : sub.BoundedBy subTime subWords)
    (divBound : divide.BoundedBy divTime divWords)

variable {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.hash.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.hash.scheme.scalar.representation
      (fun _ => sampleSource) sampler)
    {sampleTime sampleWords : Nat}
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime)
    (sampleStored : (sampler.lower port).descriptionWords ≤ sampleWords)

include mulBound addBound subBound divBound sampleCorrect sampleBound in
theorem time_bound : Interactive.TimeBound port .unit (input layout).representation
    (code layout zeroValid mul add sub divide mulBuffers addBuffers subBuffers divBuffers reserve port sampler)
    (timeBudget layout mulTime addTime subTime divTime sampleTime) := by
  have held := ((ExtractionEntry.time_bound layout zeroValid mul add mulBuffers addBuffers reserve port
    sampleCorrect mulBound addBound sampleBound).retain
    (ExtractionEntry.refines layout zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect)
    (by decide) layout.hash.scheme.scalar.representation layout.hash.scheme.wordFits (input layout).representation.fits).mono
      (Interactive.retain_time_unit_le _ _ _ _ _)
  have viewed := held.viewInput (input layout).representation (fun value => (request layout value, response layout value)) (fun _ => rfl)
  have finished := Interactive.TimeBound.compute (port := port) (cost := .unit)
    (finish layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve)
    (ExtractionArithmetic.timeBudget layout.hash.scheme addTime subTime divTime + 60 * layout.hash.scheme.width)
    (ExtractionRead.finish_time layout.hash.scheme zeroValid add sub divide addBuffers subBuffers divBuffers (arithmeticReserve reserve) addBound subBound divBound)
  have combined := viewed.seq (read_refines layout zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect) finished
  apply combined.mono
  have sizes := widths layout
  unfold timeBudget
  omega

include mulBound addBound subBound divBound sampleStored in
theorem code_bound :
    ((code layout zeroValid mul add sub divide mulBuffers addBuffers subBuffers divBuffers reserve port sampler).lower port).descriptionWords ≤
      codeBudget layout mulWords addWords subWords divWords sampleWords := by
  have body := ExtractionEntry.code_bound layout zeroValid mul add mulBuffers addBuffers reserve port sampler
    mulBound addBound sampleStored
  have held := Interactive.retain_descriptionWords_le port
    (ExtractionEntry.code layout zeroValid mul add mulBuffers addBuffers reserve port sampler)
    (Interactive.savedBuffer port (ExtractionEntry.code layout zeroValid mul add mulBuffers addBuffers reserve port sampler))
    layout.input.representation.encoding.words (EntryRead.output layout.hash.scheme).representation.encoding.words layout.hash.scheme.scalar.representation.encoding.words
  have finished := ExtractionRead.finish_words layout.hash.scheme zeroValid add sub divide addBuffers subBuffers divBuffers (arithmeticReserve reserve) addBound subBound divBound
  change descriptionWords (finish layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve).code ≤ _ at finished
  change ((read layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).descriptionWords ≤ _ at held
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  have sizes := widths layout
  unfold codeBudget
  omega

theorem names {sampleSlots : Nat}
    (mulNames : NamesBound mul.program.code slots) (addNames : NamesBound add.program.code slots) (subNames : NamesAccounted sub.program.code slots) (divNames : NamesAccounted divide.program.code slots)
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    WordIO.NamesAccounted ((code layout zeroValid mul add sub divide mulBuffers addBuffers subBuffers divBuffers reserve port sampler).lower port)
      (nameBudget slots sampleSlots) := by
  have held := Interactive.retain_names port
    (ExtractionEntry.names layout zeroValid mul add mulBuffers addBuffers reserve port sampler mulNames addNames sampleNames)
    layout.input.representation.encoding.words (EntryRead.output layout.hash.scheme).representation.encoding.words layout.hash.scheme.scalar.representation.encoding.words
  have prepared := ReorderTail.names layout.hash.scheme.entry.representation layout.hash.scheme.state.representation layout.hash.scheme.scalar.representation layout.hash.scheme.wordFits (ExtractionRead.frameFits layout.hash.scheme)
  have calculated := ExtractionArithmetic.names layout.hash.scheme slots add sub divide addBuffers subBuffers (arithmeticReserve reserve)
    addNames.accounted subNames divNames zeroValid
  have arithmetic := Retain.names calculated (ExtractionArithmetic.input layout.hash.scheme).representation.encoding.words
    layout.hash.scheme.scalar.representation.encoding.words layout.hash.scheme.state.representation.encoding.words
  have finished := (prepared.mono (show 3 ≤ nameBudget slots sampleSlots by unfold nameBudget; omega)).seq
    (arithmetic.mono (show slots ≤ nameBudget slots sampleSlots by unfold nameBudget Fresh.nameBudget; omega))
  exact held.seq (.compute finished)

theorem descriptionFits {sampleSlots : Nat} (sampleFits : (sampler.lower port).DescriptionFits)
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (samplingReserve : max slots sampleSlots + 4 < 2 ^ w) :
    ((code layout zeroValid mul add sub divide mulBuffers addBuffers subBuffers divBuffers reserve port sampler).lower port).DescriptionFits := by
  have body := ExtractionEntry.descriptionFits layout zeroValid mul add mulBuffers addBuffers reserve port sampler
    sampleFits addNames sampleNames (by omega)
  have held := Interactive.retain_descriptionFits port
    (ExtractionEntry.code layout zeroValid mul add mulBuffers addBuffers reserve port sampler)
    (Interactive.savedBuffer port (ExtractionEntry.code layout zeroValid mul add mulBuffers addBuffers reserve port sampler))
    layout.input.representation.encoding.words (EntryRead.output layout.hash.scheme).representation.encoding.words layout.hash.scheme.scalar.representation.encoding.words
    layout.hash.scheme.wordFits body (by
      have bounded := ExtractionEntry.buffers layout zeroValid mul add mulBuffers addBuffers reserve port sampler addNames sampleNames
      have hw := layout.hash.scheme.wordFits
      unfold Fresh.nameBudget at bounded
      change max 2 ((ExtractionEntry.code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).memBound < _
      omega) layout.input.representation.fits layout.hash.scheme.scalar.representation.fits (ExtractionRead.returned layout.hash.scheme).fits
  exact .seq layout.hash.scheme.wordFits held (.compute (finish layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve).description_fits)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Extraction
