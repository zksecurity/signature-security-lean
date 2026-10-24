import Proofs.Runtime.Caliper.SchnorrROMTapeFresh

/-! Derived fresh-cell overhead, including range routing, uniform I/O and cell
construction. The scalar sampler is the only supplied primitive budget. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Fresh
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} [Zero F] (layout : Layouts w F) (zeroValid : layout.scalar.valid 0)
    {scalarSource : ProbComp layout.scalar.Value} {sampler : Interactive.Code w}

def scalarTime (samplerTime : Nat) := (dropTag layout).budget.time + (samplerTime + (scalarCell layout).budget.time)
def privateTime := (privateInput layout).budget.time + (46 + (privateCell layout zeroValid).budget.time)
def timeBudget (samplerTime : Nat) :=
  (selector layout).budget.time + (scalarTime layout samplerTime + privateTime layout zeroValid + 10)
def codeBudget (samplerWords : Nat) :=
  (selector layout).budget.words + (dropTag layout).budget.words + (scalarCell layout).budget.words +
    (privateInput layout).budget.words + (privateCell layout zeroValid).budget.words + samplerWords + 320

omit [Zero F] in
theorem privateDraw_time : Interactive.TimeBound (port layout) .unit (pair layout).representation (privateDrawCode layout) 46 := by
  have retained := (natural_time layout).retain (natural_refines layout) (by decide) layout.counter.representation layout.wordFits
    (pair layout).representation.fits
  have viewed := retained.viewInput (pair layout).representation (productView layout.counter layout.counter) (fun _ => rfl)
  apply viewed.mono
  exact Interactive.retain_time_unit_le _ 1 1 1 18

theorem private_time : Interactive.TimeBound (port layout) .unit layout.counter.representation
    (privateCode layout zeroValid) (privateTime layout zeroValid) :=
  (Interactive.TimeBound.compute (port := port layout) (cost := .unit) (privateInput layout).implementation.program _
    (privateInput layout).bounded.time_le).seq
      (Interactive.Refines.compute (port layout) .unit (privateInput layout).implementation.program)
      ((privateDraw_time layout).seq (privateDraw_refines layout)
        (Interactive.TimeBound.compute (port := port layout) (cost := .unit) (privateCell layout zeroValid).implementation.program _
          (privateCell layout zeroValid).bounded.time_le))

omit [Zero F] in
theorem scalar_time
    (scalarCorrect : Interactive.Refines (port layout) .unit layout.unit.representation layout.scalar.representation
      (fun _ => scalarSource) sampler) {samplerTime : Nat}
    (scalarBound : Interactive.TimeBound (port layout) .unit layout.unit.representation sampler samplerTime) :
    Interactive.TimeBound (port layout) .unit layout.counter.representation (scalarCode layout sampler) (scalarTime layout samplerTime) :=
  (Interactive.TimeBound.compute (port := port layout) (cost := .unit) (dropTag layout).implementation.program _
    (dropTag layout).bounded.time_le).seq (Interactive.Refines.compute (port layout) .unit (dropTag layout).implementation.program)
      (scalarBound.seq scalarCorrect
        (Interactive.TimeBound.compute (port := port layout) (cost := .unit) (scalarCell layout).implementation.program _
          (scalarCell layout).bounded.time_le))

theorem time_bound
    (scalarCorrect : Interactive.Refines (port layout) .unit layout.unit.representation layout.scalar.representation
      (fun _ => scalarSource) sampler) {samplerTime : Nat}
    (scalarBound : Interactive.TimeBound (port layout) .unit layout.unit.representation sampler samplerTime) :
    Interactive.TimeBound (port layout) .unit layout.counter.representation (code layout zeroValid sampler)
      (timeBudget layout zeroValid samplerTime) := by
  have dispatched := (scalar_time layout scalarCorrect scalarBound).dispatch layout.counter.representation layout.counter.representation
    (private_time layout zeroValid) (width_pos layout.wordFits) (choice layout).representation.fits
  have viewed := dispatched.viewInput (choice layout).representation (sumView layout.counter layout.counter) (fun _ => rfl)
  have branchBound : Interactive.TimeBound (port layout) .unit (choice layout).representation
      (branchCode layout zeroValid sampler) (scalarTime layout samplerTime + privateTime layout zeroValid + 10) :=
    viewed.mono (by rw [Interactive.dispatchTime_unit]; simp only [Layouts.counter_words]; omega)
  exact (Interactive.TimeBound.compute (port := port layout) (cost := .unit) (selector layout).implementation.program _
    (selector layout).bounded.time_le).seq
      (Interactive.Refines.compute (port layout) .unit (selector layout).implementation.program) branchBound

omit [Zero F] in
theorem privateDraw_words : ((privateDrawCode layout).lower (port layout)).descriptionWords ≤ 217 := by
  have retained := Interactive.retain_descriptionWords_le (port layout) (naturalCode layout)
    (Interactive.savedBuffer (port layout) (naturalCode layout)) 1 1 1
  have natural := natural_words layout
  change ((privateDrawCode layout).lower (port layout)).descriptionWords ≤ _ at retained
  omega
theorem private_words : ((privateCode layout zeroValid).lower (port layout)).descriptionWords ≤
    (privateInput layout).budget.words + (privateCell layout zeroValid).budget.words + 221 := by
  have drawn := privateDraw_words layout
  have prepared := (privateInput layout).bounded.code_le
  have finished := (privateCell layout zeroValid).bounded.code_le
  simp only [privateCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega
omit [Zero F] in
theorem scalar_words (sampler : Interactive.Code w) : ((scalarCode layout sampler).lower (port layout)).descriptionWords ≤
    (dropTag layout).budget.words + (scalarCell layout).budget.words + (sampler.lower (port layout)).descriptionWords + 4 := by
  have prepared := (dropTag layout).bounded.code_le
  have finished := (scalarCell layout).bounded.code_le
  simp only [scalarCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega
theorem code_bound (sampler : Interactive.Code w) {samplerWords : Nat}
    (scalarBound : (sampler.lower (port layout)).descriptionWords ≤ samplerWords) :
    ((code layout zeroValid sampler).lower (port layout)).descriptionWords ≤ codeBudget layout zeroValid samplerWords := by
  have selected := (selector layout).bounded.code_le
  have scalarBounded := scalar_words layout sampler
  have privateBounded := private_words layout zeroValid
  simp only [code, branchCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, Interactive.dispatch_descriptionWords,
    WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Fresh
