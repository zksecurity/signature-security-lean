import Proofs.Runtime.Caliper.SchnorrAGMSigningComputed

/-! Signing arithmetic costs include both multiplications, subtraction,
negation, all selected arguments and the physical copies around each call. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Arithmetic
open Caliper BoundedSource
variable {w qH qS : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G]
    (layout : Layouts w M F G qH qS) (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.arithmetic.scaleArgs layout.scheme.point (fun value => value.1 • value.2))
    (sub : Implementation .unit layout.arithmetic.points layout.scheme.point (fun value => value.1 - value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)

theorem point_bounded {scaleTime scaleWords subTime subWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords) :
    (point layout zeroValid scale sub scaleBuffers reserve).BoundedBy
      (2 * scaleTime + subTime + 628 * layout.scheme.scalar.representation.encoding.words +
        492 * layout.scheme.point.representation.encoding.words)
      (2 * scaleWords + subWords + 2041 * layout.scheme.scalar.representation.encoding.words +
        1599 * layout.scheme.point.representation.encoding.words + 536) := by
  apply (((arguments_bounded layout zeroValid).then
    (BLSResponse.pointArguments_bounded layout.arithmetic scale scaleBound scaleBuffers (primitive_reserve reserve))).then subBound).mono
  all_goals rw [BLSResponse.Layouts.badInput_words]; dsimp only [Layouts.arithmetic]; omega

variable [Neg F] (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)

omit [Zero F] [SMul F G] [Sub G] in
theorem negativeChallenge_bounded {negateTime negateWords : Nat} (negateBound : negate.BoundedBy negateTime negateWords) :
    (negativeChallenge layout negate).BoundedBy
      (negateTime + 24 * layout.scheme.scalar.representation.encoding.words)
      (negateWords + 78 * layout.scheme.scalar.representation.encoding.words + 30) := by
  apply ((selectChallenge_bounded layout).then negateBound).mono <;> omega

def computedTime (scaleTime subTime negateTime : Nat) : Nat := 2 * scaleTime + subTime + negateTime + 400 * layout.width
def computedWords (scaleWords subWords negateWords : Nat) : Nat := 2 * scaleWords + subWords + negateWords + 1300 * layout.width + 700

theorem computed_bounded {scaleTime scaleWords subTime subWords negateTime negateWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (negateBound : negate.BoundedBy negateTime negateWords) :
    (computed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).BoundedBy
      (computedTime layout scaleTime subTime negateTime) (computedWords layout scaleWords subWords negateWords) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _
    (point_bounded layout zeroValid scale sub scaleBuffers reserve scaleBound subBound)
    (negativeChallenge_bounded layout negate negateBound)).mono
  all_goals
    have := layout.input_le
    dsimp only [computedTime, computedWords, Layouts.width] at *
    omega

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Arithmetic
