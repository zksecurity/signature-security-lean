import Proofs.Runtime.Caliper.SchnorrROMSigningPrepareCache
import Proofs.Runtime.Caliper.CallerBuffers

/-! Construct ROM signing's commitment from two scalar multiplications and a
subtraction, then execute all copies into the managed-cache programming frame. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Arithmetic
open Caliper BoundedSource
variable {w : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (layout : Layouts w M F G) (zeroValid : layout.scalar.valid 0)
    (scale : Implementation .unit layout.arithmetic.scaleArgs layout.point (fun value => value.1 • value.2))
    (sub : Implementation .unit layout.arithmetic.points layout.point (fun value => value.1 - value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w)

def commitment (input : Input M F G) := input.1.2 • input.2.1 - input.1.1 • input.2.2.1
def value (input : Input M F G) :=
  (((input.2.2.2.1, commitment input), input.1.1, input.2.2.2.2, ()),
    (commitment input, input.1.2), input.2.1, input.2.2.1)

def point : Implementation .unit layout.input layout.point commitment :=
  ((arguments layout zeroValid).then (BLSResponse.pointArguments layout.arithmetic scale scaleBuffers reserve)).then sub

include subBuffers in
omit [DecidableEq M] [DecidableEq G] in
theorem point_buffers : (point layout zeroValid scale sub scaleBuffers reserve).program.code.memBound ≤ max 3 slots + 1 :=
  max_le (max_le ((arguments_buffers layout zeroValid).trans (by omega))
    (BLSResponse.pointArguments_buffers layout.arithmetic scale scaleBuffers reserve)) (subBuffers.trans (by omega))

include subBuffers in
omit [DecidableEq M] [DecidableEq G] in
theorem point_nameFits : (point layout zeroValid scale sub scaleBuffers reserve).program.savedBuffer < 2 ^ w := by
  have bounded := point_buffers layout zeroValid scale sub scaleBuffers subBuffers reserve
  have := layout.wordFits
  change max 2 (point layout zeroValid scale sub scaleBuffers reserve).program.code.memBound < _
  omega

def retainPoint := (point layout zeroValid scale sub scaleBuffers reserve).program.retain (by decide)
  layout.input.representation layout.wordFits (point_nameFits layout zeroValid scale sub scaleBuffers subBuffers reserve)
  layout.duplicated.fits layout.frame.fits

def implementation : Implementation .unit layout.input layout.work value where
  preserves input valid := (finishValue layout
    (⟨commitment input, (point layout zeroValid scale sub scaleBuffers reserve).preserves input valid⟩, ⟨input, valid⟩)).property
  program := ((duplicateRealizer .unit (by decide) layout.input.representation layout.wordFits layout.duplicated.fits).then
    (retainPoint layout zeroValid scale sub scaleBuffers subBuffers reserve)).then (finish layout)

theorem buffers : (implementation layout zeroValid scale sub scaleBuffers subBuffers reserve).program.code.memBound ≤ max 3 slots + 2 := by
  have duplicated := (Assembly.code_names (Assembly.reads (w := w) 0 0 layout.input.representation.encoding.words ++
    Assembly.reads 0 0 layout.input.representation.encoding.words) 1
    ((Assembly.sourcesBound_append _ _ _).mpr
      ⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩)).2
  have computed := point_buffers layout zeroValid scale sub scaleBuffers subBuffers reserve
  have retained := (point layout zeroValid scale sub scaleBuffers reserve).program.retain_buffers (by decide)
    layout.input.representation layout.wordFits (point_nameFits layout zeroValid scale sub scaleBuffers subBuffers reserve)
    layout.duplicated.fits layout.frame.fits
  have finished := finish_buffers layout
  change (retainPoint layout zeroValid scale sub scaleBuffers subBuffers reserve).code.memBound ≤ _ at retained
  change max (max _ (retainPoint layout zeroValid scale sub scaleBuffers subBuffers reserve).code.memBound) (finish layout).code.memBound ≤ _
  exact max_le (max_le (duplicated.trans (by omega)) (retained.trans (by omega))) (finished.trans (by omega))

theorem names (names : Nat) (scaleNames : NamesAccounted scale.program.code names) (subNames : NamesAccounted sub.program.code names) :
    NamesAccounted (implementation layout zeroValid scale sub scaleBuffers subBuffers reserve).program.code names :=
  ((Assembly.code_namesAccounted _ names
    ((Assembly.sourcesBound_append _ _ _).mpr
      ⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩)).seq
    (Retain.names (((arguments_names layout zeroValid names).seq
      (BLSResponse.pointArguments_names layout.arithmetic names scale scaleNames scaleBuffers reserve)).seq subNames) _ _ _)).seq
    (finish_names layout names)

def timeBudget (scaleTime subTime : Nat) := 2 * scaleTime + subTime + 1200 * layout.width
def codeBudget (scaleWords subWords : Nat) := 2 * scaleWords + subWords + 3900 * layout.width + 610

variable {scaleTime subTime scaleWords subWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)

include scaleBound subBound in
omit [DecidableEq M] [DecidableEq G] in
theorem point_bounded : (point layout zeroValid scale sub scaleBuffers reserve).BoundedBy
    (2 * scaleTime + subTime + 1120 * layout.width) (2 * scaleWords + subWords + 3640 * layout.width + 536) := by
  apply (((arguments_bounded layout zeroValid).then
    (BLSResponse.pointArguments_bounded layout.arithmetic scale scaleBound scaleBuffers reserve)).then subBound).mono
  all_goals
    rw [BLSResponse.Layouts.badInput_words]
    dsimp only [Layouts.arithmetic]
    unfold Layouts.width
    omega

include scaleBound subBound in
theorem bounded : (implementation layout zeroValid scale sub scaleBuffers subBuffers reserve).BoundedBy
    (timeBudget layout scaleTime subTime) (codeBudget layout scaleWords subWords) := by
  have computed := point_bounded layout zeroValid scale sub scaleBuffers reserve scaleBound subBound
  have copiedTime := (point layout zeroValid scale sub scaleBuffers reserve).program.retain_time_unit_le
    layout.input.representation layout.wordFits (point_nameFits layout zeroValid scale sub scaleBuffers subBuffers reserve)
    layout.duplicated.fits layout.frame.fits
  have copiedWords := (point layout zeroValid scale sub scaleBuffers reserve).program.retain_descriptionWords_le
    (by decide) layout.input.representation layout.wordFits (point_nameFits layout zeroValid scale sub scaleBuffers subBuffers reserve)
    layout.duplicated.fits layout.frame.fits
  have duplicateWords := Assembly.code_descriptionWords_le
    (Assembly.reads (w := w) 0 0 layout.input.representation.encoding.words ++ Assembly.reads 0 0 layout.input.representation.encoding.words)
  have finishedWords := finish_words layout
  have inputSize := layout.input_le
  have workSize := layout.work_le
  have pointSize : layout.point.representation.encoding.words ≤ layout.width := by unfold Layouts.width; omega
  constructor
  · intro input
    have copied := copiedTime (input, input)
    have pointTime := computed.time_le input
    have finished := finish_time layout
      (⟨commitment input.val, (point layout zeroValid scale sub scaleBuffers reserve).preserves input.val input.property⟩, input)
    have duplicateTime := Assembly.code_time_unit_le
      (Assembly.reads (w := w) 0 0 layout.input.representation.encoding.words ++ Assembly.reads 0 0 layout.input.representation.encoding.words)
    simp only [List.length_append, Assembly.reads_length] at duplicateTime
    change (duplicateRealizer .unit (by decide) layout.input.representation layout.wordFits layout.duplicated.fits).time input ≤ _ at duplicateTime
    dsimp only at copied
    change (retainPoint layout zeroValid scale sub scaleBuffers subBuffers reserve).time (input, input) ≤ _ at copied
    change _ + (retainPoint layout zeroValid scale sub scaleBuffers subBuffers reserve).time (input, input) +
      (finish layout).time (⟨commitment input.val, (point layout zeroValid scale sub scaleBuffers reserve).preserves input.val input.property⟩, input) ≤ _
    unfold timeBudget
    omega
  · have pointWords := computed.code_le
    simp only [List.length_append, Assembly.reads_length] at duplicateWords
    change descriptionWords (duplicateRealizer .unit (by decide) layout.input.representation layout.wordFits layout.duplicated.fits).code ≤ _ at duplicateWords
    change descriptionWords (retainPoint layout zeroValid scale sub scaleBuffers subBuffers reserve).code ≤ _ at copiedWords
    change descriptionWords ((_ ;; _) ;; _) ≤ _
    rw [descriptionWords_seq, descriptionWords_seq]
    unfold codeBudget
    omega

end Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Arithmetic
