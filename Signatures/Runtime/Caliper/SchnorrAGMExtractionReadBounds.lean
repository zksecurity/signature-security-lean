import Signatures.Runtime.Caliper.SchnorrAGMExtractionRead

/-! Costs and descriptor acceptance for the complete read-and-extract code.
Every retained scalar, state copy and arithmetic branch contributes to the
derived bounds; only primitive budgets and name extents are supplied. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.ExtractionRead
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def timeBudget (addTime subTime divTime sampleTime : Nat) : Nat :=
  EntryRead.timeBudget layout addTime sampleTime + ExtractionArithmetic.timeBudget layout addTime subTime divTime + 100 * layout.width
def codeBudget (addWords subWords divWords sampleWords : Nat) : Nat :=
  EntryRead.codeBudget layout addWords sampleWords + ExtractionArithmetic.codeBudget layout addWords subWords divWords + 400 * layout.width + 100
def nameBudget (slots sampleSlots : Nat) : Nat := max 5 (Fresh.nameBudget slots sampleSlots)

variable [Zero F] [DecidableEq M] [DecidableEq G]
theorem widths :
    (Read.input layout).representation.encoding.words ≤ 2 * layout.width ∧
    (EntryRead.output layout).representation.encoding.words ≤ layout.width ∧
    layout.entry.representation.encoding.words + layout.state.representation.encoding.words + layout.scalar.representation.encoding.words ≤ 2 * layout.width ∧
    (ExtractionArithmetic.input layout).representation.encoding.words ≤ 2 * layout.width ∧
    layout.scalar.representation.encoding.words ≤ layout.width ∧ layout.state.representation.encoding.words ≤ layout.width := by
  have entry := EntryRead.output_size layout
  have parts : layout.entry.representation.encoding.words + layout.state.representation.encoding.words ≤ layout.width := entry
  have scalar := ExtractionArithmetic.sizes layout
  exact ⟨(Read.sizes layout).1, entry, by omega, scalar.1, scalar.2, by omega⟩

variable [Add F] [Sub F] [Div F] [DecidableEq F]
    (zeroValid : layout.scalar.valid 0)
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    (sub : Implementation .unit layout.affine layout.scalar (fun value => value.1 - value.2))
    (divide : Implementation .unit layout.affine layout.scalar (fun value => value.1 / value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (divBuffers : divide.program.code.memBound ≤ slots) (reserve : slots + 3 < 2 ^ w)
    {addTime addWords subTime subWords divTime divWords : Nat}
    (addBound : add.BoundedBy addTime addWords) (subBound : sub.BoundedBy subTime subWords)
    (divBound : divide.BoundedBy divTime divWords)

include addBound subBound divBound in
omit [DecidableEq F] in
theorem finish_time (value) :
    (finish layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve).time value ≤
      ExtractionArithmetic.timeBudget layout addTime subTime divTime + 60 * layout.width := by
  have prepared := ReorderTail.time layout.entry.representation layout.state.representation layout.scalar.representation
    layout.wordFits (frameFits layout) ((⟨value.1.val.1, value.1.property.1⟩, ⟨value.1.val.2, value.1.property.2⟩), value.2)
  have held := (ExtractionArithmetic.implementation layout add sub divide addBuffers subBuffers reserve zeroValid).program.retain_time_unit_le
    layout.state.representation layout.wordFits (arithmetic_nameFits layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve)
    (arithmeticFrame layout).fits (Read.output layout).representation.fits (arguments layout value)
  have calculated := (ExtractionArithmetic.bounded layout add sub divide addBuffers subBuffers reserve addBound subBound divBound zeroValid).time_le
    (arguments layout value).1
  change (prepare layout).time value ≤ _ at prepared
  change (arithmetic layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve).time (arguments layout value) ≤ _ at held
  change (prepare layout).time value + (arithmetic layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve).time (arguments layout value) ≤ _
  have sizes := widths layout
  omega

include addBound subBound divBound in
omit [DecidableEq F] in
theorem finish_words :
    descriptionWords (finish layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve).code ≤
      ExtractionArithmetic.codeBudget layout addWords subWords divWords + 200 * layout.width + 54 := by
  have prepared := ReorderTail.words layout.entry.representation layout.state.representation layout.scalar.representation
    layout.wordFits (frameFits layout)
  have held := (ExtractionArithmetic.implementation layout add sub divide addBuffers subBuffers reserve zeroValid).program.retain_descriptionWords_le
    (by decide) layout.state.representation layout.wordFits (arithmetic_nameFits layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve)
    (arithmeticFrame layout).fits (Read.output layout).representation.fits
  have calculated := (ExtractionArithmetic.bounded layout add sub divide addBuffers subBuffers reserve addBound subBound divBound zeroValid).code_le
  change descriptionWords (prepare layout).code ≤ _ at prepared
  change descriptionWords (arithmetic layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve).code ≤ _ at held
  change descriptionWords ((prepare layout).code ;; (arithmetic layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve).code) ≤ _
  rw [descriptionWords_seq]
  have sizes := widths layout
  omega

variable {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scalar.representation
      (fun _ => sampleSource) sampler)
    {sampleTime sampleWords : Nat}
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime)
    (sampleStored : (sampler.lower port).descriptionWords ≤ sampleWords)

include addBound subBound divBound sampleCorrect sampleBound in
theorem time_bound : Interactive.TimeBound port .unit (input layout).representation
    (code layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve port sampler)
    (timeBudget layout addTime subTime divTime sampleTime) := by
  have held := ((EntryRead.time_bound layout zeroValid add addBuffers ((Nat.le_add_right slots 3).trans_lt reserve) port
    sampleCorrect addBound.time_le sampleBound).retain
    (EntryRead.refines layout zeroValid add addBuffers ((Nat.le_add_right slots 3).trans_lt reserve) port sampleCorrect)
    (by decide) layout.scalar.representation layout.wordFits (input layout).representation.fits).mono
      (Interactive.retain_time_unit_le _ _ _ _ _)
  have viewed := held.viewInput (input layout).representation (fun value => (readInput layout value, response layout value)) (fun _ => rfl)
  have finished := Interactive.TimeBound.compute (port := port) (cost := .unit)
    (finish layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve)
    (ExtractionArithmetic.timeBudget layout addTime subTime divTime + 60 * layout.width)
    (finish_time layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve addBound subBound divBound)
  have combined := viewed.seq (read_refines layout zeroValid add addBuffers reserve port sampleCorrect) finished
  apply combined.mono
  have sizes := widths layout
  unfold timeBudget
  omega

include addBound subBound divBound sampleStored in
theorem code_bound :
    ((code layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve port sampler).lower port).descriptionWords ≤
      codeBudget layout addWords subWords divWords sampleWords := by
  have body := EntryRead.code_bound layout zeroValid add addBuffers ((Nat.le_add_right slots 3).trans_lt reserve) port sampler
    addBound.code_le sampleStored
  have held := Interactive.retain_descriptionWords_le port
    (EntryRead.code layout zeroValid add addBuffers ((Nat.le_add_right slots 3).trans_lt reserve) port sampler)
    (Interactive.savedBuffer port (EntryRead.code layout zeroValid add addBuffers ((Nat.le_add_right slots 3).trans_lt reserve) port sampler))
    (Read.input layout).representation.encoding.words (EntryRead.output layout).representation.encoding.words layout.scalar.representation.encoding.words
  have finished := finish_words layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve addBound subBound divBound
  change ((read layout zeroValid add addBuffers reserve port sampler).lower port).descriptionWords ≤ _ at held
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  have sizes := widths layout
  unfold codeBudget
  omega

theorem names {sampleSlots : Nat}
    (addNames : NamesBound add.program.code slots) (subNames : NamesAccounted sub.program.code slots) (divNames : NamesAccounted divide.program.code slots)
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    WordIO.NamesAccounted ((code layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve port sampler).lower port)
      (nameBudget slots sampleSlots) := by
  have held := Interactive.retain_names port
    (EntryRead.names layout zeroValid add addBuffers ((Nat.le_add_right slots 3).trans_lt reserve) port sampler addNames sampleNames)
    (Read.input layout).representation.encoding.words (EntryRead.output layout).representation.encoding.words layout.scalar.representation.encoding.words
  have prepared := ReorderTail.names layout.entry.representation layout.state.representation layout.scalar.representation layout.wordFits (frameFits layout)
  have calculated := ExtractionArithmetic.names layout slots add sub divide addBuffers subBuffers reserve
    addNames.accounted subNames divNames zeroValid
  have arithmetic := Retain.names calculated (ExtractionArithmetic.input layout).representation.encoding.words
    layout.scalar.representation.encoding.words layout.state.representation.encoding.words
  have finished := (prepared.mono (show 3 ≤ nameBudget slots sampleSlots by unfold nameBudget; omega)).seq
    (arithmetic.mono (show slots ≤ nameBudget slots sampleSlots by unfold nameBudget Fresh.nameBudget; omega))
  exact held.seq (.compute finished)

theorem descriptionFits {sampleSlots : Nat} (sampleFits : (sampler.lower port).DescriptionFits)
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (samplingReserve : max slots sampleSlots + 3 < 2 ^ w) :
    ((code layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve port sampler).lower port).DescriptionFits := by
  have body := EntryRead.descriptionFits layout zeroValid add addBuffers ((Nat.le_add_right slots 3).trans_lt reserve) port sampler
    sampleFits addNames sampleNames (by omega)
  have held := Interactive.retain_descriptionFits port
    (EntryRead.code layout zeroValid add addBuffers ((Nat.le_add_right slots 3).trans_lt reserve) port sampler)
    (Interactive.savedBuffer port (EntryRead.code layout zeroValid add addBuffers ((Nat.le_add_right slots 3).trans_lt reserve) port sampler))
    (Read.input layout).representation.encoding.words (EntryRead.output layout).representation.encoding.words layout.scalar.representation.encoding.words
    layout.wordFits body (by
      have bounded := EntryRead.buffers layout zeroValid add addBuffers ((Nat.le_add_right slots 3).trans_lt reserve) port sampler addNames sampleNames
      have hw := layout.wordFits
      unfold Fresh.nameBudget at bounded
      change max 2 ((EntryRead.code layout zeroValid add addBuffers ((Nat.le_add_right slots 3).trans_lt reserve) port sampler).lower port).memBound < _
      omega) (Read.input layout).representation.fits layout.scalar.representation.fits (returned layout).fits
  exact .seq layout.wordFits held (.compute (finish layout zeroValid add sub divide addBuffers subBuffers divBuffers reserve).description_fits)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.ExtractionRead
