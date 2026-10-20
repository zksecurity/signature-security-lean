import Signatures.Runtime.Caliper.SchnorrAGMSigningArguments

/-! The signing commitment and affine coefficient are computed by actual
scalar-multiplication, subtraction and negation routines. Projections, input
retention and result pairing are generated Caliper instructions. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Arithmetic
open Caliper BoundedSource
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def selectChallenge : Implementation .unit layout.input layout.scheme.scalar (fun value => value.1.1) :=
  (Implementation.first (by decide) layout.scheme.affine layout.base layout.scheme.wordFits _).then
    (Implementation.first (by decide) layout.scheme.scalar layout.scheme.scalar layout.scheme.wordFits _)

theorem selectChallenge_buffers : (selectChallenge layout).program.code.memBound ≤ 2 :=
  max_le (Implementation.first_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)
theorem selectChallenge_names (names : Nat) : NamesAccounted (selectChallenge layout).program.code names :=
  (Implementation.first_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)
theorem selectChallenge_bounded : (selectChallenge layout).BoundedBy
    (24 * layout.scheme.scalar.representation.encoding.words)
    (78 * layout.scheme.scalar.representation.encoding.words + 29) := by
  apply ((Implementation.first_boundedBy _ _ _ _).then (Implementation.first_boundedBy _ _ _ _)).mono
  · change 8 * (layout.scheme.scalar.representation.encoding.words + layout.scheme.scalar.representation.encoding.words) +
      8 * layout.scheme.scalar.representation.encoding.words ≤ _
    omega
  · change 26 * (layout.scheme.scalar.representation.encoding.words + layout.scheme.scalar.representation.encoding.words) + 14 +
      (26 * layout.scheme.scalar.representation.encoding.words + 14) + 1 ≤ _
    omega

theorem primitive_reserve {slots : Nat} (reserve : slots + 4 < 2 ^ w) : slots + 3 < 2 ^ w := by omega

variable [Zero F] [SMul F G] [Sub G] [Neg F]
    (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.arithmetic.scaleArgs layout.scheme.point (fun value => value.1 • value.2))
    (sub : Implementation .unit layout.arithmetic.points layout.scheme.point (fun value => value.1 - value.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

def point : Implementation .unit layout.input layout.scheme.point
    (fun value => value.1.2 • value.2.1 - value.1.1 • value.2.2.1) :=
  ((arguments layout zeroValid).then
    (BLSResponse.pointArguments layout.arithmetic scale scaleBuffers (primitive_reserve reserve))).then sub

def negativeChallenge : Implementation .unit layout.input layout.scheme.scalar (fun value => -value.1.1) :=
  (selectChallenge layout).then negate

include subBuffers in
omit [Neg F] in
theorem point_buffers : (point layout zeroValid scale sub scaleBuffers reserve).program.code.memBound ≤ max 3 slots + 1 :=
  max_le (max_le ((arguments_buffers layout zeroValid).trans (by omega))
    (BLSResponse.pointArguments_buffers layout.arithmetic scale scaleBuffers (primitive_reserve reserve))) (subBuffers.trans (by omega))

include negateBuffers in
omit [Zero F] [SMul F G] [Sub G] in
theorem negativeChallenge_buffers : (negativeChallenge layout negate).program.code.memBound ≤ max 2 slots :=
  max_le ((selectChallenge_buffers layout).trans (Nat.le_max_left _ _)) (negateBuffers.trans (Nat.le_max_right _ _))

def computed : Implementation .unit layout.input layout.computed
    (fun value => (value.1.2 • value.2.1 - value.1.1 • value.2.2.1, -value.1.1)) :=
  (point layout zeroValid scale sub scaleBuffers reserve).pair (negativeChallenge layout negate) (by decide) layout.scheme.wordFits
    (BLSResponse.nameFits layout.arithmetic _ (point_buffers layout zeroValid scale sub scaleBuffers subBuffers reserve)
      (by have := layout.scheme.wordFits; omega))
    (BLSResponse.nameFits layout.arithmetic _ (negativeChallenge_buffers layout negate negateBuffers)
      (by have := layout.scheme.wordFits; omega))
    layout.duplicated.fits
    (layout.fits_of_le (by have := layout.input_le; unfold Layouts.width at *; omega))
    layout.computed.representation.fits

theorem computed_buffers :
    (computed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code.memBound ≤ max 3 slots + 2 := by
  have bound := Implementation.pair_buffers (point layout zeroValid scale sub scaleBuffers reserve) (negativeChallenge layout negate)
    layout.scheme.wordFits
    (BLSResponse.nameFits layout.arithmetic _ (point_buffers layout zeroValid scale sub scaleBuffers subBuffers reserve)
      (by have := layout.scheme.wordFits; omega))
    (BLSResponse.nameFits layout.arithmetic _ (negativeChallenge_buffers layout negate negateBuffers)
      (by have := layout.scheme.wordFits; omega))
    layout.duplicated.fits
    (layout.fits_of_le (by have := layout.input_le; unfold Layouts.width at *; omega))
    layout.computed.representation.fits
    (point_buffers layout zeroValid scale sub scaleBuffers subBuffers reserve)
    (negativeChallenge_buffers layout negate negateBuffers)
  exact bound.trans (by omega)

theorem computed_names (names : Nat) (scaleNames : NamesAccounted scale.program.code names)
    (subNames : NamesAccounted sub.program.code names) (negateNames : NamesAccounted negate.program.code names) :
    NamesAccounted (computed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _
    (((arguments_names layout zeroValid names).seq
      (BLSResponse.pointArguments_names layout.arithmetic names scale scaleNames scaleBuffers (primitive_reserve reserve))).seq subNames)
    ((selectChallenge_names layout names).seq negateNames)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Arithmetic
