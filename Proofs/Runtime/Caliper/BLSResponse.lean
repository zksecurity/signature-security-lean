import Proofs.Runtime.Caliper.BLSResponseLayout
import Proofs.Runtime.LazyAGMReply

/-! Constructed scalar/group response code for both BLS AGM branches. Only
scalar multiplication and group addition are supplied as primitive code.
All argument selection, copies, retained inputs and composition are generated. -/

namespace Signatures.Runtime.CaliperBackend.BLSResponse

open Caliper BoundedSource

section Implementation

variable {w : Nat} {F G : Type} [SMul F G] [Add G]
    (layout : Layouts w F G)
    (scale : Implementation .unit layout.scaleArgs layout.point (fun value => value.1 • value.2))
    (add : Implementation .unit layout.points layout.point (fun value => value.1 + value.2))

def good (signing : Bool) : Implementation .unit layout.config layout.point
    (fun value => value.1 • (if signing then value.2.2 else value.2.1)) :=
  (goodArguments layout signing).then scale

def term (first : Bool) : Implementation .unit layout.badInput layout.point
    (fun value => (if first then value.1.1 else value.1.2) • (if first then value.2.2.2 else value.2.2.1)) :=
  (termArguments layout first).then scale

variable {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w)

include scaleBuffers in
omit [Add G] in
theorem term_buffers (first : Bool) : (term layout scale first).program.code.memBound ≤ max 3 slots :=
  max_le ((termArguments_buffers layout first).trans (Nat.le_max_left _ _))
    (scaleBuffers.trans (Nat.le_max_right _ _))

def pointArguments : Implementation .unit layout.badInput layout.points
    (fun value => (value.1.1 • value.2.2.2, value.1.2 • value.2.2.1)) :=
  (term layout scale true).pair (term layout scale false) (by decide) layout.wordFits
    (nameFits layout _ (term_buffers layout scale scaleBuffers true) (by have h := layout.wordFits; omega))
    (nameFits layout _ (term_buffers layout scale scaleBuffers false) (by have h := layout.wordFits; omega))
    (layout.fits_of_le (by rw [Layouts.badInput_words]; omega))
    (layout.fits_of_le (by rw [Layouts.badInput_words]; omega)) _

def point : Implementation .unit layout.badInput layout.point
    (fun value => value.1.1 • value.2.2.2 + value.1.2 • value.2.2.1) :=
  (pointArguments layout scale scaleBuffers reserve).then add

omit [Add G] in
theorem pointArguments_buffers : (pointArguments layout scale scaleBuffers reserve).program.code.memBound ≤ max 3 slots + 1 := by
  have bound := Implementation.pair_buffers (term layout scale true) (term layout scale false) layout.wordFits
    (nameFits layout _ (term_buffers layout scale scaleBuffers true) (by have h := layout.wordFits; omega))
    (nameFits layout _ (term_buffers layout scale scaleBuffers false) (by have h := layout.wordFits; omega))
    (layout.fits_of_le (by rw [Layouts.badInput_words]; omega))
    (layout.fits_of_le (by rw [Layouts.badInput_words]; omega))
    (layout.fits_of_le (by omega))
    (term_buffers layout scale scaleBuffers true) (term_buffers layout scale scaleBuffers false)
  exact bound.trans (by omega)

variable (addBuffers : add.program.code.memBound ≤ slots)

include addBuffers in
theorem point_buffers : (point layout scale add scaleBuffers reserve).program.code.memBound ≤ max 3 slots + 1 :=
  max_le (pointArguments_buffers layout scale scaleBuffers reserve) (addBuffers.trans (by omega))

def signingArguments : Implementation .unit layout.badInput layout.scaleArgs
    (fun value => (value.2.1, value.1.1 • value.2.2.2 + value.1.2 • value.2.2.1)) :=
  (kappa layout).pair (point layout scale add scaleBuffers reserve) (by decide) layout.wordFits
    (nameFits layout _ (kappa_buffers layout) (by have h := layout.wordFits; omega))
    (nameFits layout _ (point_buffers layout scale add scaleBuffers reserve addBuffers) (by have h := layout.wordFits; omega))
    (layout.fits_of_le (by rw [Layouts.badInput_words]; omega))
    (layout.fits_of_le (by rw [Layouts.badInput_words]; omega)) _

def bad (signing : Bool) : Implementation .unit layout.badInput layout.point
    (fun value => if signing then value.2.1 • (value.1.1 • value.2.2.2 + value.1.2 • value.2.2.1)
      else value.1.1 • value.2.2.2 + value.1.2 • value.2.2.1) := by
  cases signing
  · exact point layout scale add scaleBuffers reserve
  · exact (signingArguments layout scale add scaleBuffers reserve addBuffers).then scale

end Implementation
section Source

variable {F G G₂ : Type} [Field F] [AddCommGroup G] [Module F G]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq F] [DecidableEq G] [DecidableEq G₂]
    {M : Type} [DecidableEq M]

theorem good_source (cost : PrimitiveCosts) (signing : Bool) (rho : F) (g X : G) :
    rho • (if signing then X else g) =
      (LazyAGM.goodResponse signing).denote (arithmetic F G G₂ M M cost) (rho, (g, X), ()) := by
  rw [LazyAGM.goodResponse_denote]
  cases signing <;> rfl

theorem bad_source (cost : PrimitiveCosts) (signing : Bool) (masks : F × F) (kappa : F) (g X : G) :
    (if signing then kappa • (masks.1 • X + masks.2 • g) else masks.1 • X + masks.2 • g) =
      (LazyAGM.badResponse signing).denote (arithmetic F G G₂ M M cost) (masks, (kappa, g, X), ()) :=
  (LazyAGM.badResponse_denote cost signing masks g X kappa).symm

end Source
end Signatures.Runtime.CaliperBackend.BLSResponse
