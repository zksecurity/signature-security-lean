import Signatures.Runtime.Caliper.SchnorrAGMSigningFinish
import Signatures.Runtime.BackendSchnorrAGMSigning

/-! Complete signing arithmetic: duplicate and retain the sampled request,
execute the cryptographic routines, and construct the source work frame. No
whole signing routine or uncharged state-copy operation is supplied. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Arithmetic
open Caliper BoundedSource
variable {w qH qS : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [Neg F]
    (layout : Layouts w M F G qH qS) (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.arithmetic.scaleArgs layout.scheme.point (fun value => value.1 • value.2))
    (sub : Implementation .unit layout.arithmetic.points layout.scheme.point (fun value => value.1 - value.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

def value (input : Input M F G) : Work M F G :=
  let point := input.1.2 • input.2.1 - input.1.1 • input.2.2.1
  (((input.2.2.2.1, point), (input.1.1, false, 0, 0), input.2.2.2.2.1, ()),
    (point, input.1.2), (input.1.2, -input.1.1), input.2.2.2.1, input.2.2.2.2.2)

theorem computed_nameFits :
    (computed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.savedBuffer < 2 ^ w := by
  have bound := computed_buffers layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve
  have hw := layout.scheme.wordFits
  change max 2 (computed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code.memBound < _
  omega

def retainComputed :=
  (computed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.retain (by decide)
    layout.input.representation layout.scheme.wordFits
    (computed_nameFits layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve)
    layout.duplicated.fits layout.frame.fits

def implementation : Implementation .unit layout.input layout.work value where
  preserves input valid := (finishValue layout zeroValid
    (⟨(input.1.2 • input.2.1 - input.1.1 • input.2.2.1, -input.1.1),
      (computed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).preserves input valid⟩,
      ⟨input, valid⟩)).property
  program := ((duplicateRealizer .unit (by decide) layout.input.representation layout.scheme.wordFits layout.duplicated.fits).then
    (retainComputed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve)).then (finish layout zeroValid)

theorem buffers : (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code.memBound ≤ max 3 slots + 3 := by
  have duplicated := (Assembly.code_names (Assembly.reads (w := w) 0 0 layout.input.representation.encoding.words ++
    Assembly.reads 0 0 layout.input.representation.encoding.words) 1
    ((Assembly.sourcesBound_append _ _ _).mpr
      ⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩)).2
  have body := computed_buffers layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve
  have held := (Retain.code_names (computed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code
    (max 2 (computed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code.memBound)
    layout.input.representation.encoding.words layout.computed.representation.encoding.words layout.input.representation.encoding.words
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)).2
  have finished := finish_buffers layout zeroValid
  change max (max _ (retainComputed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).code.memBound)
    (finish layout zeroValid).code.memBound ≤ _
  change (retainComputed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).code.memBound ≤ _ at held
  exact max_le (max_le (duplicated.trans (by omega)) (held.trans (by omega))) (finished.trans (by omega))

theorem names (slotsNamed : Nat) (scaleNames : NamesAccounted scale.program.code slotsNamed)
    (subNames : NamesAccounted sub.program.code slotsNamed) (negateNames : NamesAccounted negate.program.code slotsNamed) :
    NamesAccounted (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code slotsNamed :=
  ((Assembly.code_namesAccounted _ slotsNamed
    ((Assembly.sourcesBound_append _ _ _).mpr
      ⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩)).seq
      (Retain.names (computed_names layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve
        slotsNamed scaleNames subNames negateNames) _ _ _)).seq (finish_names layout zeroValid slotsNamed)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Arithmetic

namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Arithmetic
variable {M F G : Type} [Field F] [AddCommGroup G] [Module F G]

theorem source_original (input : Input M F G) : value input = Signatures.Runtime.SchnorrAGM.Native.Signing.arithmeticValue input := rfl

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Arithmetic
