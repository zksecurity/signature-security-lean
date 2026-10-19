import Signatures.Runtime.Caliper.BLSSetup

/-! Setup budgets are derived from projection, pairing and initialization code.
Only the bad branch's individual public-key scale routine supplies a budget. -/

namespace Signatures.Runtime.CaliperBackend.BLSSetup
open Caliper BoundedSource

variable {w : Nat} {M F G K : Type} (layout : Layouts w M F G K)

theorem points_bounded : (points layout).BoundedBy
    (8 * layout.scheme.response.points.representation.encoding.words)
    (26 * layout.scheme.response.points.representation.encoding.words + 14) :=
  Implementation.first_boundedBy _ _ _ _

theorem publicKey_bounded : (publicKey layout).BoundedBy
    (24 * layout.key.representation.encoding.words) (78 * layout.key.representation.encoding.words + 29) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals simp only [Layout.prod_words]; omega

theorem generator_bounded : (generator layout).BoundedBy
    (24 * layout.key.representation.encoding.words) (78 * layout.key.representation.encoding.words + 29) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals simp only [Layout.prod_words]; omega

theorem scalar_bounded : (scalar layout).BoundedBy
    (8 * layout.scheme.cache.value.representation.encoding.words)
    (26 * layout.scheme.cache.value.representation.encoding.words + 14) :=
  Implementation.first_boundedBy _ _ _ _

theorem sampledPoints_bounded : (sampledPoints layout).BoundedBy
    (8 * layout.challenge.representation.encoding.words + 8 * layout.scheme.response.points.representation.encoding.words)
    (26 * layout.challenge.representation.encoding.words + 26 * layout.scheme.response.points.representation.encoding.words + 29) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (points_bounded layout)).mono <;> omega

theorem sampledGenerator_bounded : (sampledGenerator layout).BoundedBy
    (8 * layout.challenge.representation.encoding.words + 24 * layout.key.representation.encoding.words)
    (26 * layout.challenge.representation.encoding.words + 78 * layout.key.representation.encoding.words + 44) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (generator_bounded layout)).mono <;> omega

theorem goodPrefix_bounded : (goodPrefix layout).BoundedBy (160 * layout.width) (600 * layout.width + 200) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (publicKey_bounded layout) (points_bounded layout)).mono
  all_goals have := layout.sizes; omega

theorem config_bounded : (config layout).BoundedBy (200 * layout.width) (700 * layout.width + 200) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (scalar_bounded layout) (sampledPoints_bounded layout)).mono
  all_goals have := layout.sizes; omega

theorem arguments_bounded : (arguments layout).BoundedBy (200 * layout.width) (700 * layout.width + 200) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (scalar_bounded layout) (sampledGenerator_bounded layout)).mono
  all_goals have := layout.sizes; omega

theorem good_bounded : (good layout).BoundedBy (200 * layout.width) (700 * layout.width + 250) := by
  apply ((goodPrefix_bounded layout).then (BLSInitialization.implementation_bounded layout.scheme.good layout.key layout.goodFits)).mono
  all_goals have := layout.sizes; dsimp only [Layouts.goodOutput] at this; omega

variable [SMul F K]
    (scale : Implementation .unit layout.scaleArgs layout.key (fun value => value.1 • value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)
    {scaleTime scaleWords : Nat} (scaleBound : scale.BoundedBy scaleTime scaleWords)

include scaleBound in
theorem signingKey_bounded : (signingKey layout scale).BoundedBy
    (scaleTime + 200 * layout.width) (scaleWords + 700 * layout.width + 201) := by
  apply ((arguments_bounded layout).then scaleBound).mono <;> omega

include scaleBound in
theorem badPrefix_bounded : (badPrefix layout scale scaleBuffers reserve).BoundedBy
    (scaleTime + 600 * layout.width) (scaleWords + 2000 * layout.width + 600) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (signingKey_bounded layout scale scaleBound) (config_bounded layout)).mono
  all_goals have := layout.sizes; omega

include scaleBound in
theorem badLocal_bounded : (badLocal layout scale scaleBuffers reserve).BoundedBy
    (scaleTime + 700 * layout.width) (scaleWords + 2200 * layout.width + 650) := by
  apply ((badPrefix_bounded layout scale scaleBuffers reserve scaleBound).then
    (BLSInitialization.implementation_bounded layout.scheme.bad layout.key layout.badFits)).mono
  all_goals have := layout.sizes; dsimp only [Layouts.badOutput] at this; omega

end Signatures.Runtime.CaliperBackend.BLSSetup
