import Proofs.Runtime.Caliper.BLSResponseBounds

/-! Generated registers and buffer descriptors for the BLS responses. Primitive
name reservations are separate from instruction counts and copied word widths. -/

namespace Signatures.Runtime.CaliperBackend.BLSResponse

open Caliper BoundedSource

variable {w : Nat} {F G : Type} (layout : Layouts w F G) (names : Nat)

theorem pointSelect_names (second : Bool) : NamesAccounted (pointSelect layout second).program.code names := by
  cases second
  · exact Implementation.first_names _ _ _ _ _
  · exact Implementation.second_names _ _ _ _ _

theorem scalarSelect_names (first : Bool) : NamesAccounted (scalarSelect layout first).program.code names := by
  cases first
  · exact Implementation.second_names _ _ _ _ _
  · exact Implementation.first_names _ _ _ _ _

theorem goodScalar_names : NamesAccounted (goodScalar layout).program.code names := Implementation.first_names _ _ _ _ _
theorem goodPoint_names (signing : Bool) : NamesAccounted (goodPoint layout signing).program.code names :=
  (Implementation.second_names _ _ _ _ _).seq (pointSelect_names layout names signing)
theorem badScalar_names (first : Bool) : NamesAccounted (badScalar layout first).program.code names :=
  (Implementation.first_names _ _ _ _ _).seq (scalarSelect_names layout names first)
theorem badPoint_names (first : Bool) : NamesAccounted (badPoint layout first).program.code names :=
  (Implementation.second_names _ _ _ _ _).seq (goodPoint_names layout names first)
theorem kappa_names : NamesAccounted (kappa layout).program.code names :=
  (Implementation.second_names _ _ _ _ _).seq (goodScalar_names layout names)

theorem goodArguments_names (signing : Bool) : NamesAccounted (goodArguments layout signing).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (goodScalar_names layout names) (goodPoint_names layout names signing)
theorem termArguments_names (first : Bool) : NamesAccounted (termArguments layout first).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (badScalar_names layout names first) (badPoint_names layout names first)

variable [SMul F G] [Add G]
    (scale : Implementation .unit layout.scaleArgs layout.point (fun value => value.1 • value.2))
    (add : Implementation .unit layout.points layout.point (fun value => value.1 + value.2))
    (scaleNames : NamesAccounted scale.program.code names) (addNames : NamesAccounted add.program.code names)

include scaleNames in
omit [Add G] in
theorem good_names (signing : Bool) : NamesAccounted (good layout scale signing).program.code names :=
  (goodArguments_names layout names signing).seq scaleNames

include scaleNames in
omit [Add G] in
theorem term_names (first : Bool) : NamesAccounted (term layout scale first).program.code names :=
  (termArguments_names layout names first).seq scaleNames

variable {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 3 < 2 ^ w)

include scaleNames in
omit [Add G] in
theorem pointArguments_names : NamesAccounted (pointArguments layout scale scaleBuffers reserve).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (term_names layout names scale scaleNames true) (term_names layout names scale scaleNames false)

include scaleNames addNames in
theorem point_names : NamesAccounted (point layout scale add scaleBuffers reserve).program.code names :=
  (pointArguments_names layout names scale scaleNames scaleBuffers reserve).seq addNames

variable (addBuffers : add.program.code.memBound ≤ slots)

include scaleNames addNames in
theorem signingArguments_names : NamesAccounted (signingArguments layout scale add scaleBuffers reserve addBuffers).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (kappa_names layout names)
    (point_names layout names scale add scaleNames addNames scaleBuffers reserve)

include scaleNames addNames in
theorem bad_names (signing : Bool) : NamesAccounted (bad layout scale add scaleBuffers reserve addBuffers signing).program.code names := by
  cases signing
  · exact point_names layout names scale add scaleNames addNames scaleBuffers reserve
  · exact (signingArguments_names layout names scale add scaleNames addNames scaleBuffers reserve addBuffers).seq scaleNames

include scaleBuffers in
omit [Add G] in
theorem good_buffers (signing : Bool) : (good layout scale signing).program.code.memBound ≤ max 3 slots :=
  max_le ((goodArguments_buffers layout signing).trans (Nat.le_max_left _ _)) (scaleBuffers.trans (Nat.le_max_right _ _))

theorem signingArguments_buffers :
    (signingArguments layout scale add scaleBuffers reserve addBuffers).program.code.memBound ≤ max 3 slots + 2 := by
  have bound := Implementation.pair_buffers (kappa layout) (point layout scale add scaleBuffers reserve)
    layout.wordFits
    (nameFits layout _ (kappa_buffers layout) (by have h := layout.wordFits; omega))
    (nameFits layout _ (point_buffers layout scale add scaleBuffers reserve addBuffers) (by have h := layout.wordFits; omega))
    (layout.fits_of_le (by rw [Layouts.badInput_words]; omega))
    (layout.fits_of_le (by rw [Layouts.badInput_words]; omega))
    (layout.fits_of_le (by omega)) (kappa_buffers layout) (point_buffers layout scale add scaleBuffers reserve addBuffers)
  exact bound.trans (by omega)

theorem bad_buffers (signing : Bool) : (bad layout scale add scaleBuffers reserve addBuffers signing).program.code.memBound ≤ max 3 slots + 2 := by
  cases signing
  · exact (point_buffers layout scale add scaleBuffers reserve addBuffers).trans (by omega)
  · exact max_le (signingArguments_buffers layout scale add scaleBuffers reserve addBuffers) (scaleBuffers.trans (by omega))

end Signatures.Runtime.CaliperBackend.BLSResponse
