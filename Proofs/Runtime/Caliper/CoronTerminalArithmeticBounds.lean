import Proofs.Runtime.Caliper.CoronTerminalArithmetic

/-! Extraction costs and names derived from the projections, copied argument
pairs and two supplied group routines. No complete-extractor bound is assumed. -/
namespace Signatures.Runtime.CaliperBackend.CoronTerminal
open Caliper BoundedSource
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G : Type}
    (layout : CoronService.Layouts w M F G randomBound qS)

theorem scalar_bounded : (scalar layout).BoundedBy (24 * width layout) (78 * width layout + 44) := by
  have sizes := base_sizes layout
  apply (((Implementation.first_boundedBy _ _ _ _).then (Implementation.first_boundedBy _ _ _ _)).then
    (Implementation.first_boundedBy _ _ _ _)).mono
  · change (8 * (CacheRead.output layout.service.cache).representation.encoding.words +
      8 * layout.service.cache.value.representation.encoding.words) + 8 * layout.cache.value.representation.encoding.words ≤ _
    omega
  · change ((26 * (CacheRead.output layout.service.cache).representation.encoding.words + 14) +
      (26 * layout.service.cache.value.representation.encoding.words + 14) + 1) +
      (26 * layout.cache.value.representation.encoding.words + 14) + 1 ≤ _
    omega
theorem signature_bounded : (signature layout).BoundedBy (16 * width layout) (52 * width layout + 29) := by
  have sizes := base_sizes layout
  apply ((Implementation.second_boundedBy _ _ _ _).then (Implementation.first_boundedBy _ _ _ _)).mono
  · change 8 * layout.response.points.representation.encoding.words + 8 * layout.point.representation.encoding.words ≤ _
    omega
  · change (26 * layout.response.points.representation.encoding.words + 14) +
      (26 * layout.point.representation.encoding.words + 14) + 1 ≤ _
    omega
theorem challenge_bounded : (challenge layout).BoundedBy (16 * width layout) (52 * width layout + 29) := by
  have sizes := base_sizes layout
  apply ((Implementation.second_boundedBy _ _ _ _).then (Implementation.second_boundedBy _ _ _ _)).mono
  · change 8 * layout.response.points.representation.encoding.words + 8 * layout.point.representation.encoding.words ≤ _
    omega
  · change (26 * layout.response.points.representation.encoding.words + 14) +
      (26 * layout.point.representation.encoding.words + 14) + 1 ≤ _
    omega
theorem operands_bounded : (operands layout).BoundedBy (144 * width layout) (468 * width layout + 197) := by
  have sizes := base_sizes layout
  have inputSize := returned_le layout
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (scalar_bounded layout) (challenge_bounded layout)).mono <;> omega

variable (names : Nat)
theorem scalar_names : NamesAccounted (scalar layout).program.code names :=
  ((Implementation.first_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)).seq
    (Implementation.first_names _ _ _ _ _)
theorem signature_names : NamesAccounted (signature layout).program.code names :=
  (Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)
theorem challenge_names : NamesAccounted (challenge layout).program.code names :=
  (Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _)
theorem operands_names : NamesAccounted (operands layout).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (scalar_names layout names) (challenge_names layout names)

variable [SMul F G]
    (scale : Implementation .unit layout.response.scaleArgs layout.point (fun value => value.1 • value.2))
    {scaleTime scaleWords : Nat} (scaleBound : scale.BoundedBy scaleTime scaleWords)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 3 < 2 ^ w)

include scaleBound in
theorem scaled_bounded : (scaled layout scale).BoundedBy
    (scaleTime + 144 * width layout) (scaleWords + 468 * width layout + 198) := by
  apply ((operands_bounded layout).then scaleBound).mono <;> omega
include scaleBound in
theorem subtractionArgs_bounded : (subtractionArgs layout scale scaleBuffers reserve).BoundedBy
    (scaleTime + 264 * width layout) (scaleWords + 858 * width layout + 351) := by
  have sizes := base_sizes layout
  have inputSize := returned_le layout
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (signature_bounded layout)
    (scaled_bounded layout scale scaleBound)).mono <;> omega

variable [Sub G] (sub : Implementation .unit layout.response.points layout.point (fun value => value.1 - value.2))
    {subTime subWords : Nat} (subBound : sub.BoundedBy subTime subWords)

include scaleBound subBound in
theorem extract_bounded : (extract layout scale scaleBuffers reserve sub).BoundedBy
    (scaleTime + subTime + 264 * width layout) (scaleWords + subWords + 858 * width layout + 352) := by
  apply ((subtractionArgs_bounded layout scale scaleBound scaleBuffers reserve).then subBound).mono <;> omega

theorem extract_names (scaleNames : NamesAccounted scale.program.code names)
    (subNames : NamesAccounted sub.program.code names) :
    NamesAccounted (extract layout scale scaleBuffers reserve sub).program.code names :=
  (Implementation.pair_names _ _ _ _ _ _ _ _ (signature_names layout names)
    ((operands_names layout names).seq scaleNames)).seq subNames

end Signatures.Runtime.CaliperBackend.CoronTerminal
