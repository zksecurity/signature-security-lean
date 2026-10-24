import Proofs.Runtime.Caliper.SchnorrAGMHashPrepareBounds

/-! Resource bounds for a complete well-shaped hash request: compute the affine
explanation, retain and restore the original state, then read or sample a challenge. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Hash
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G I : Type} [Zero F] [Mul F] [Add F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : Layouts w M F G qH qS) (zeroValid : layout.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (port : Interactive.Port w spec)

def timeBudget (mulTime addTime sampleTime : Nat) : Nat :=
  prepareTime layout mulTime addTime + Read.timeBudget layout.scheme addTime sampleTime
def codeBudget (mulWords addWords sampleWords : Nat) : Nat :=
  prepareWords layout mulWords addWords + Read.codeBudget layout.scheme addWords sampleWords + 2

theorem time_bound {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler) {mulTime mulWords addTime addWords sampleTime : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound port .unit layout.input.representation
      (code layout zeroValid mul add mulBuffers addBuffers reserve port sampler) (timeBudget layout mulTime addTime sampleTime) := by
  have prepared := Interactive.TimeBound.compute (port := port) (cost := .unit)
    (prepare layout zeroValid mul add mulBuffers addBuffers reserve) (prepareTime layout mulTime addTime)
    (prepare_time layout zeroValid mul add mulBuffers addBuffers reserve mulBound addBound)
  have cached := Read.time_bound layout.scheme zeroValid add addBuffers (by omega) port sampleCorrect addBound.time_le sampleBound
  exact prepared.seq (Interactive.Refines.compute port .unit (prepare layout zeroValid mul add mulBuffers addBuffers reserve)) cached

theorem code_bound (sampler : Interactive.Code w) {mulTime mulWords addTime addWords sampleWords : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (sampleBound : (sampler.lower port).descriptionWords ≤ sampleWords) :
    ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).descriptionWords ≤
      codeBudget layout mulWords addWords sampleWords := by
  have prepared := prepare_words layout zeroValid mul add mulBuffers addBuffers reserve mulBound addBound
  have cached := Read.code_bound layout.scheme zeroValid add addBuffers (by omega) port sampler addBound.code_le sampleBound
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names (sampler : Interactive.Code w) {sampleSlots : Nat}
    (mulNames : NamesBound mul.program.code slots) (addNames : NamesBound add.program.code slots)
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    WordIO.NamesAccounted ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port)
      (max 5 (Fresh.nameBudget slots sampleSlots)) := by
  have prepared := (prepare_names layout zeroValid mul add mulBuffers addBuffers reserve slots mulNames.accounted addNames.accounted).mono
    (show slots ≤ max 5 (Fresh.nameBudget slots sampleSlots) by unfold Fresh.nameBudget; omega)
  exact (WordIO.NamesAccounted.compute prepared).seq
    (Read.names layout.scheme zeroValid add addBuffers (by omega) port sampler addNames sampleNames)

theorem buffers (sampler : Interactive.Code w) {sampleSlots : Nat}
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).memBound ≤
      max 11 (Fresh.nameBudget slots sampleSlots + 3) := by
  have prepared := prepare_buffers layout zeroValid mul add mulBuffers addBuffers reserve
  have cached := Read.buffers layout.scheme zeroValid add addBuffers (by omega) port sampler addNames sampleNames
  change max (prepare layout zeroValid mul add mulBuffers addBuffers reserve).code.memBound
    ((Read.code layout.scheme zeroValid add addBuffers (by omega) port sampler).lower port).memBound ≤ _
  unfold Fresh.nameBudget at *
  omega

theorem descriptionFits (sampler : Interactive.Code w) {sampleSlots : Nat}
    (sampleFits : (sampler.lower port).DescriptionFits)
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (sampleReserve : max slots sampleSlots + 4 < 2 ^ w) :
    ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).DescriptionFits :=
  .seq layout.scheme.wordFits (.compute (prepare layout zeroValid mul add mulBuffers addBuffers reserve).description_fits)
    (Read.descriptionFits layout.scheme zeroValid add addBuffers (by omega) port sampler sampleFits addNames sampleNames (by omega))

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Hash
