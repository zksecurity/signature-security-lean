import Proofs.Runtime.Caliper.SchnorrROMTapeCaller

/-! Derived time and stored-code bounds for complete caller queries. Prefix
construction, range retention, replay and executed decoding are all charged. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Caller
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} [Zero F] (layout : Layouts w F) (zeroValid : layout.scalar.valid 0)

def retainTime : Nat := 8 * (Read.input layout).representation.encoding.words +
  8 * (Read.output layout).representation.encoding.words + 12
def privateTime (samplerTime : Nat) : Nat := (prepare layout zeroValid).budget.time +
  (Query.timeBudget layout zeroValid samplerTime + retainTime layout + (finish layout).budget.time)
def scalarTime (samplerTime : Nat) : Nat := (scalarPacket layout zeroValid).budget.time +
  (Query.timeBudget layout zeroValid samplerTime + (Reply.scalarDecoder layout).budget.time)
def privateWords (samplerWords : Nat) : Nat := (prepare layout zeroValid).budget.words +
  Query.codeBudget layout zeroValid samplerWords + (finish layout).budget.words +
  26 * (Read.input layout).representation.encoding.words + 26 * (Read.output layout).representation.encoding.words + 84
def scalarWords (samplerWords : Nat) : Nat := (scalarPacket layout zeroValid).budget.words +
  Query.codeBudget layout zeroValid samplerWords + (Reply.scalarDecoder layout).budget.words + 4

variable {scalarSource : ProbComp layout.scalar.Value} {sampler : Interactive.Code w}
    (scalarCorrect : Interactive.Refines (Fresh.port layout) .unit layout.unit.representation layout.scalar.representation
      (fun _ => scalarSource) sampler)

include scalarCorrect in
theorem retained_time {samplerTime : Nat}
    (scalarBound : Interactive.TimeBound (Fresh.port layout) .unit layout.unit.representation sampler samplerTime) :
    Interactive.TimeBound (Fresh.port layout) .unit (retainedInput layout).representation
      (retainedCode layout zeroValid sampler) (Query.timeBudget layout zeroValid samplerTime + retainTime layout) := by
  have retained := (Query.time_bound layout zeroValid scalarCorrect scalarBound).retain
    (Query.refines layout zeroValid scalarCorrect) (by decide) (Reply.range layout).representation layout.wordFits
      (retainedInput layout).representation.fits
  have viewed := retained.viewInput (retainedInput layout).representation
    (productView (Read.input layout) (Reply.range layout)) (fun _ => rfl)
  apply viewed.mono
  have bounded := Interactive.retain_time_unit_le (w := w)
    (Interactive.savedBuffer (Fresh.port layout) (Query.code layout zeroValid sampler))
    (Read.input layout).representation.encoding.words (Read.output layout).representation.encoding.words
    (Reply.range layout).representation.encoding.words (Query.timeBudget layout zeroValid samplerTime)
  have rangeSize : (Reply.range layout).representation.encoding.words = 1 := rfl
  simpa only [retainTime, Nat.add_assoc, rangeSize, Nat.mul_one, WordIO.Costs.unit] using bounded

include scalarCorrect in
theorem private_time {samplerTime : Nat}
    (scalarBound : Interactive.TimeBound (Fresh.port layout) .unit layout.unit.representation sampler samplerTime) :
    Interactive.TimeBound (Fresh.port layout) .unit (privateInput layout).representation
      (privateCode layout zeroValid sampler) (privateTime layout zeroValid samplerTime) :=
  (Interactive.TimeBound.compute (port := Fresh.port layout) (cost := .unit)
    (prepare layout zeroValid).implementation.program _ (prepare layout zeroValid).bounded.time_le).seq
      (Interactive.Refines.compute (Fresh.port layout) .unit (prepare layout zeroValid).implementation.program)
      ((retained_time layout zeroValid scalarCorrect scalarBound).seq (retained_refines layout zeroValid scalarCorrect)
        (Interactive.TimeBound.compute (port := Fresh.port layout) (cost := .unit)
          (finish layout).implementation.program _ (finish layout).bounded.time_le))

include scalarCorrect in
theorem scalar_time {samplerTime : Nat}
    (scalarBound : Interactive.TimeBound (Fresh.port layout) .unit layout.unit.representation sampler samplerTime) :
    Interactive.TimeBound (Fresh.port layout) .unit (Read.store layout).representation
      (scalarCode layout zeroValid sampler) (scalarTime layout zeroValid samplerTime) :=
  (Interactive.TimeBound.compute (port := Fresh.port layout) (cost := .unit)
    (scalarPacket layout zeroValid).implementation.program _ (scalarPacket layout zeroValid).bounded.time_le).seq
      (Interactive.Refines.compute (Fresh.port layout) .unit (scalarPacket layout zeroValid).implementation.program)
      ((Query.time_bound layout zeroValid scalarCorrect scalarBound).seq (Query.refines layout zeroValid scalarCorrect)
        (Interactive.TimeBound.compute (port := Fresh.port layout) (cost := .unit)
          (Reply.scalarDecoder layout).implementation.program _ (Reply.scalarDecoder layout).bounded.time_le))

theorem retained_words (sampler : Interactive.Code w) :
    ((retainedCode layout zeroValid sampler).lower (Fresh.port layout)).descriptionWords ≤
      ((Query.code layout zeroValid sampler).lower (Fresh.port layout)).descriptionWords +
      26 * (Read.input layout).representation.encoding.words + 26 * (Read.output layout).representation.encoding.words + 80 := by
  have bounded := Interactive.retain_descriptionWords_le (Fresh.port layout) (Query.code layout zeroValid sampler)
    (Interactive.savedBuffer (Fresh.port layout) (Query.code layout zeroValid sampler))
    (Read.input layout).representation.encoding.words (Read.output layout).representation.encoding.words
    (Reply.range layout).representation.encoding.words
  change ((retainedCode layout zeroValid sampler).lower (Fresh.port layout)).descriptionWords ≤
    ((Query.code layout zeroValid sampler).lower (Fresh.port layout)).descriptionWords +
      26 * (Read.input layout).representation.encoding.words + 26 * (Read.output layout).representation.encoding.words + 39 * 1 + 41 at bounded
  omega

theorem private_words (sampler : Interactive.Code w) {samplerWords : Nat}
    (scalarBound : (sampler.lower (Fresh.port layout)).descriptionWords ≤ samplerWords) :
    ((privateCode layout zeroValid sampler).lower (Fresh.port layout)).descriptionWords ≤ privateWords layout zeroValid samplerWords := by
  have queried := Query.code_bound layout zeroValid sampler scalarBound
  have retained := retained_words layout zeroValid sampler
  have prepared := (prepare layout zeroValid).bounded.code_le
  have finished := (finish layout).bounded.code_le
  simp only [privateCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  dsimp only [privateWords]
  omega

theorem scalar_words (sampler : Interactive.Code w) {samplerWords : Nat}
    (scalarBound : (sampler.lower (Fresh.port layout)).descriptionWords ≤ samplerWords) :
    ((scalarCode layout zeroValid sampler).lower (Fresh.port layout)).descriptionWords ≤ scalarWords layout zeroValid samplerWords := by
  have queried := Query.code_bound layout zeroValid sampler scalarBound
  have prepared := (scalarPacket layout zeroValid).bounded.code_le
  have finished := (Reply.scalarDecoder layout).bounded.code_le
  simp only [scalarCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  dsimp only [scalarWords]
  omega

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Caller
