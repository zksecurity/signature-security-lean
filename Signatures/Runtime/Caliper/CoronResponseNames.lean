import Signatures.Runtime.Caliper.CoronResponseBounds

/-! Name reservations and buffer footprints for the constructed Coron replies.
The only external bounds concern the two supplied group routines. -/
namespace Signatures.Runtime.CaliperBackend.CoronResponse
open Caliper BoundedSource
variable {w qS : Nat} {F G : Type} (layout : Layouts w F G qS) (names : Nat)

theorem scalarValue_names : NamesAccounted (scalarValue layout).program.code names :=
  (Implementation.first_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)
theorem coinValue_names : NamesAccounted (coinValue layout).program.code names :=
  (Implementation.first_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _)
theorem configuration_names : NamesAccounted (configuration layout).program.code names := Implementation.second_names _ _ _ _ _
theorem tailPoints_names : NamesAccounted (tailPoints layout).program.code names :=
  (configuration_names layout names).seq (Implementation.second_names _ _ _ _ _)
theorem basePoint_names : NamesAccounted (basePoint layout).program.code names :=
  (configuration_names layout names).seq (Implementation.first_names _ _ _ _ _)
theorem keyPoint_names : NamesAccounted (keyPoint layout).program.code names :=
  (tailPoints_names layout names).seq (Implementation.first_names _ _ _ _ _)
theorem challengePoint_names : NamesAccounted (challengePoint layout).program.code names :=
  (tailPoints_names layout names).seq (Implementation.second_names _ _ _ _ _)
theorem selectedPoint_names (signing : Bool) : NamesAccounted (selectedPoint layout signing).program.code names := by
  cases signing
  · exact basePoint_names layout names
  · exact keyPoint_names layout names
theorem test_names : NamesAccounted (test layout).program.code names :=
  (coinValue_names layout names).seq (Finite.isZero_names qS layout.wordFits layout.coinFits names)
theorem arguments_names (signing : Bool) : NamesAccounted (arguments layout signing).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (scalarValue_names layout names) (selectedPoint_names layout names signing)

variable [Zero G] (zeroValid : layout.point.valid 0)
theorem zeroPoint_names : NamesAccounted (zeroPoint layout zeroValid).program.code names :=
  Implementation.constant_names layout.input layout.point ⟨0, zeroValid⟩ layout.wordFits names
theorem offset_names : NamesAccounted (offset layout zeroValid).program.code names :=
  GuardedBranch.implementation_names (hw := layout.wordFits) (test layout)
    (nameFits layout _ (test_buffers layout) (by have := layout.wordFits; omega)) layout.duplicateFits layout.tagFits
    ((challengePoint layout).restrictInput (fun value => condition value = true))
    ((zeroPoint layout zeroValid).restrictInput (fun value => condition value = false))
    (test_names layout names) (challengePoint_names layout names) (zeroPoint_names layout names zeroValid)

variable [SMul F G]
    (scale : Implementation .unit layout.scaleArgs layout.point (fun value => value.1 • value.2))
    (scaleNames : NamesAccounted scale.program.code names)

include scaleNames in
omit [Zero G] in
theorem scaled_names (signing : Bool) : NamesAccounted (scaled layout scale signing).program.code names :=
  (arguments_names layout names signing).seq scaleNames

include scaleNames in
theorem sign_names : NamesAccounted (sign layout zeroValid scale).program.code names :=
  GuardedBranch.implementation_names (hw := layout.wordFits) (test layout)
    (nameFits layout _ (test_buffers layout) (by have := layout.wordFits; omega)) layout.duplicateFits layout.tagFits
    ((zeroPoint layout zeroValid).restrictInput (fun value => condition value = true))
    ((scaled layout scale true).restrictInput (fun value => condition value = false))
    (test_names layout names) (zeroPoint_names layout names zeroValid) (scaled_names layout names scale scaleNames true)

variable {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 3 < 2 ^ w)

include scaleNames in
theorem hashArguments_names : NamesAccounted (hashArguments layout zeroValid scale scaleBuffers reserve).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (scaled_names layout names scale scaleNames false) (offset_names layout names zeroValid)

include scaleBuffers in
theorem sign_buffers : (sign layout zeroValid scale).program.code.memBound ≤ max 3 slots := by
  have bounded := GuardedBranch.implementation_buffers (hw := layout.wordFits) (test layout)
    (nameFits layout _ (test_buffers layout) (by have := layout.wordFits; omega)) layout.duplicateFits layout.tagFits
    ((zeroPoint layout zeroValid).restrictInput (fun value => condition value = true))
    ((scaled layout scale true).restrictInput (fun value => condition value = false))
    (test_buffers layout) (Implementation.constant_buffers layout.input layout.point ⟨0, zeroValid⟩ layout.wordFits)
    (scaled_buffers layout scale scaleBuffers true)
  exact bounded.trans (by omega)

theorem hashArguments_buffers : (hashArguments layout zeroValid scale scaleBuffers reserve).program.code.memBound ≤ max 3 slots + 1 := by
  have bounded := Implementation.pair_buffers (scaled layout scale false) (offset layout zeroValid) layout.wordFits
    (nameFits layout _ (scaled_buffers layout scale scaleBuffers false) (by have := layout.wordFits; omega))
    (nameFits layout _ (offset_buffers layout zeroValid) (by have := layout.wordFits; omega))
    layout.duplicateFits (layout.fits_of_le (by rw [Layouts.input_words]; unfold Layouts.width; omega))
    (layout.fits_of_le (by omega))
    (scaled_buffers layout scale scaleBuffers false) (offset_buffers layout zeroValid)
  exact bounded.trans (by omega)

variable [Add G] (add : Implementation .unit layout.points layout.point (fun value => value.1 + value.2))
    (addNames : NamesAccounted add.program.code names) (addBuffers : add.program.code.memBound ≤ slots)

include scaleNames addNames in
theorem reply_names (signing : Bool) : NamesAccounted (reply layout zeroValid scale add scaleBuffers reserve signing).program.code names := by
  cases signing
  · exact (hashArguments_names layout names zeroValid scale scaleNames scaleBuffers reserve).seq addNames
  · exact sign_names layout names zeroValid scale scaleNames

include addBuffers in
theorem reply_buffers (signing : Bool) :
    (reply layout zeroValid scale add scaleBuffers reserve signing).program.code.memBound ≤ max 3 slots + 1 := by
  cases signing
  · exact max_le (hashArguments_buffers layout zeroValid scale scaleBuffers reserve) (addBuffers.trans (by omega))
  · exact (sign_buffers layout zeroValid scale scaleBuffers).trans (by omega)

end Signatures.Runtime.CaliperBackend.CoronResponse
