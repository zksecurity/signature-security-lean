import Signatures.Runtime.Caliper.PairBounds

/-! Fixed-width layouts for the scalar/group computation in BLS replies.
The single storage bound covers all generated projection and pairing frames. -/

namespace Signatures.Runtime.CaliperBackend.BLSResponse

open Caliper BoundedSource

structure Layouts (w : Nat) (F G : Type) where
  scalar : Layout w F
  point : Layout w G
  wordFits : 16 < 2 ^ w
  storageFits : 16 * (scalar.representation.encoding.words + point.representation.encoding.words) < 2 ^ w

namespace Layouts

variable {w : Nat} {F G : Type} (layout : Layouts w F G)

theorem fits_of_le {words : Nat}
    (bound : words ≤ 16 * (layout.scalar.representation.encoding.words + layout.point.representation.encoding.words)) :
    words < 2 ^ w := bound.trans_lt layout.storageFits

def scaleArgs : Layout w (F × G) := layout.scalar.prod layout.point (layout.fits_of_le (by omega))
def points : Layout w (G × G) := layout.point.prod layout.point (layout.fits_of_le (by omega))
def scalars : Layout w (F × F) := layout.scalar.prod layout.scalar (layout.fits_of_le (by omega))
def config : Layout w (F × (G × G)) := layout.scalar.prod layout.points (layout.fits_of_le (by
  change _ + (_ + _) ≤ _; omega))
def badInput : Layout w ((F × F) × (F × (G × G))) := layout.scalars.prod layout.config (layout.fits_of_le (by
  change (_ + _) + (_ + (_ + _)) ≤ _; omega))

@[simp] theorem scaleArgs_words : layout.scaleArgs.representation.encoding.words =
    layout.scalar.representation.encoding.words + layout.point.representation.encoding.words := rfl
@[simp] theorem points_words : layout.points.representation.encoding.words = 2 * layout.point.representation.encoding.words := by
  change _ + _ = _; omega
@[simp] theorem scalars_words : layout.scalars.representation.encoding.words = 2 * layout.scalar.representation.encoding.words := by
  change _ + _ = _; omega
@[simp] theorem config_words : layout.config.representation.encoding.words =
    layout.scalar.representation.encoding.words + 2 * layout.point.representation.encoding.words := by
  change _ + (_ + _) = _; omega
@[simp] theorem badInput_words : layout.badInput.representation.encoding.words =
    3 * layout.scalar.representation.encoding.words + 2 * layout.point.representation.encoding.words := by
  change (_ + _) + (_ + (_ + _)) = _; omega

end Layouts

variable {w : Nat} {F G : Type} (layout : Layouts w F G)

def pointSelect (second : Bool) : Implementation .unit layout.points layout.point
    (fun value => if second then value.2 else value.1) := by
  cases second
  · exact Implementation.first (by decide) layout.point layout.point layout.wordFits _
  · exact Implementation.second (by decide) layout.point layout.point layout.wordFits _

def scalarSelect (first : Bool) : Implementation .unit layout.scalars layout.scalar
    (fun value => if first then value.1 else value.2) := by
  cases first
  · exact Implementation.second (by decide) layout.scalar layout.scalar layout.wordFits _
  · exact Implementation.first (by decide) layout.scalar layout.scalar layout.wordFits _

def goodScalar : Implementation .unit layout.config layout.scalar Prod.fst :=
  Implementation.first (by decide) layout.scalar layout.points layout.wordFits _

def goodPoint (signing : Bool) : Implementation .unit layout.config layout.point
    (fun value => if signing then value.2.2 else value.2.1) :=
  (Implementation.second (by decide) layout.scalar layout.points layout.wordFits _).then (pointSelect layout signing)

def badScalar (first : Bool) : Implementation .unit layout.badInput layout.scalar
    (fun value => if first then value.1.1 else value.1.2) :=
  (Implementation.first (by decide) layout.scalars layout.config layout.wordFits _).then (scalarSelect layout first)

def badPoint (first : Bool) : Implementation .unit layout.badInput layout.point
    (fun value => if first then value.2.2.2 else value.2.2.1) :=
  (Implementation.second (by decide) layout.scalars layout.config layout.wordFits _).then (goodPoint layout first)

def kappa : Implementation .unit layout.badInput layout.scalar (fun value => value.2.1) :=
  (Implementation.second (by decide) layout.scalars layout.config layout.wordFits _).then (goodScalar layout)

theorem pointSelect_buffers (second : Bool) : (pointSelect layout second).program.code.memBound ≤ 2 := by
  cases second
  · exact Implementation.first_buffers _ _ _ _ _
  · exact Implementation.second_buffers _ _ _ _ _
theorem scalarSelect_buffers (first : Bool) : (scalarSelect layout first).program.code.memBound ≤ 2 := by
  cases first
  · exact Implementation.second_buffers _ _ _ _ _
  · exact Implementation.first_buffers _ _ _ _ _
theorem goodScalar_buffers : (goodScalar layout).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
theorem goodPoint_buffers (signing : Bool) : (goodPoint layout signing).program.code.memBound ≤ 2 :=
  max_le (Implementation.second_buffers _ _ _ _ _) (pointSelect_buffers layout signing)
theorem badScalar_buffers (first : Bool) : (badScalar layout first).program.code.memBound ≤ 2 :=
  max_le (Implementation.first_buffers _ _ _ _ _) (scalarSelect_buffers layout first)
theorem badPoint_buffers (first : Bool) : (badPoint layout first).program.code.memBound ≤ 2 :=
  max_le (Implementation.second_buffers _ _ _ _ _) (goodPoint_buffers layout first)
theorem kappa_buffers : (kappa layout).program.code.memBound ≤ 2 :=
  max_le (Implementation.second_buffers _ _ _ _ _) (goodScalar_buffers layout)

include layout in
theorem nameFits {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (body : Implementation .unit input output f) {buffers : Nat}
    (bound : body.program.code.memBound ≤ buffers) (fits : buffers < 2 ^ w) : body.program.savedBuffer < 2 ^ w := by
  have width := layout.wordFits
  change max 2 body.program.code.memBound < 2 ^ w
  omega

def goodArguments (signing : Bool) : Implementation .unit layout.config layout.scaleArgs
    (fun value => (value.1, if signing then value.2.2 else value.2.1)) :=
  (goodScalar layout).pair (goodPoint layout signing) (by decide) layout.wordFits
    (nameFits layout _ (goodScalar_buffers layout) (by have h := layout.wordFits; omega))
    (nameFits layout _ (goodPoint_buffers layout signing) (by have h := layout.wordFits; omega))
    (layout.fits_of_le (by rw [Layouts.config_words]; omega))
    (layout.fits_of_le (by rw [Layouts.config_words]; omega)) _

def termArguments (first : Bool) : Implementation .unit layout.badInput layout.scaleArgs
    (fun value => (if first then value.1.1 else value.1.2, if first then value.2.2.2 else value.2.2.1)) :=
  (badScalar layout first).pair (badPoint layout first) (by decide) layout.wordFits
    (nameFits layout _ (badScalar_buffers layout first) (by have h := layout.wordFits; omega))
    (nameFits layout _ (badPoint_buffers layout first) (by have h := layout.wordFits; omega))
    (layout.fits_of_le (by rw [Layouts.badInput_words]; omega))
    (layout.fits_of_le (by rw [Layouts.badInput_words]; omega)) _

theorem goodArguments_buffers (signing : Bool) : (goodArguments layout signing).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (goodScalar_buffers layout) (goodPoint_buffers layout signing)
theorem termArguments_buffers (first : Bool) : (termArguments layout first).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (badScalar_buffers layout first) (badPoint_buffers layout first)

end Signatures.Runtime.CaliperBackend.BLSResponse
