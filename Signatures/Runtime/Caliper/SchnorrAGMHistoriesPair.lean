import Signatures.Runtime.Caliper.SchnorrAGMHistoriesSelect

/-! Pair construction for the history-update pipeline. Generated intermediate
frames fit the declared width, and saved buffers lie beyond each callee's
mutation footprint. Each use includes all physical duplication and retention. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Histories
open Caliper BoundedSource
variable {w qH qS : Nat} {M F G A B : Type} (layout : Layouts w M F G qH qS)
    {firstLayout : Layout w A} {secondLayout : Layout w B} {f : Work M F G → A} {g : Work M F G → B}
    (first : Implementation .unit layout.input firstLayout f) (second : Implementation .unit layout.input secondLayout g)
    (firstBuffers : first.program.code.memBound ≤ 8) (secondBuffers : second.program.code.memBound ≤ 8)
    (firstWidth : firstLayout.representation.encoding.words ≤ 3 * layout.width)
    (secondWidth : secondLayout.representation.encoding.words ≤ 3 * layout.width)

include layout in
theorem nameFits {X Y : Type} {input : Layout w X} {output : Layout w Y} {h : X → Y}
    (body : Implementation .unit input output h) (bound : body.program.code.memBound ≤ 8) : body.program.savedBuffer < 2 ^ w := by
  have := layout.scheme.wordFits
  change max 2 body.program.code.memBound < 2 ^ w
  omega

def combine : Implementation .unit layout.input
    (firstLayout.prod secondLayout (layout.fits_of_le (by omega))) (fun input => (f input, g input)) :=
  first.pair second (by decide) layout.scheme.wordFits (nameFits layout first firstBuffers) (nameFits layout second secondBuffers)
    (layout.fits_of_le (by have := layout.input_le; omega))
    (layout.fits_of_le (by have := layout.input_le; omega)) (layout.fits_of_le (by omega))

theorem combine_buffers {firstCount secondCount : Nat}
    (firstBound : first.program.code.memBound ≤ firstCount) (secondBound : second.program.code.memBound ≤ secondCount) :
    (combine layout first second firstBuffers secondBuffers firstWidth secondWidth).program.code.memBound ≤ max 2 (max firstCount secondCount) + 1 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ firstBound secondBound

theorem combine_names (slots : Nat) (firstNames : NamesAccounted first.program.code slots) (secondNames : NamesAccounted second.program.code slots) :
    NamesAccounted (combine layout first second firstBuffers secondBuffers firstWidth secondWidth).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ firstNames secondNames

theorem combine_bounded {firstTime firstWords secondTime secondWords : Nat}
    (firstBound : first.BoundedBy firstTime firstWords) (secondBound : second.BoundedBy secondTime secondWords) :
    (combine layout first second firstBuffers secondBuffers firstWidth secondWidth).BoundedBy
      (firstTime + secondTime + 312 * layout.width) (firstWords + secondWords + 1014 * layout.width + 124) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ firstBound secondBound).mono
  all_goals have := layout.input_le; omega

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Histories
