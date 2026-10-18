import Signatures.Runtime.Caliper.WordPort

/-! Word-width checks for the complete I/O program description. All names and
immediate operands in local code and in the I/O envelope must fit a word.
-/

namespace Signatures.Runtime.CaliperBackend.WordIO

open Caliper

variable {w : Nat}

def Code.checkDescription (code : Code w) : Bool := code.description.all (fun token => decide (token < 2 ^ w))

theorem Code.checkDescription_eq_true (code : Code w) : code.checkDescription = true ↔ code.DescriptionFits := by
  simp [checkDescription, DescriptionFits, List.all_eq_true]

theorem Code.DescriptionFits.compute {code : Stmt w} (fits : CaliperBackend.DescriptionFits code) :
    (Code.compute code).DescriptionFits := by
  intro token member
  simp only [Code.description, List.mem_cons] at member
  rcases member with rfl | member
  · positivity
  · exact fits token member

theorem Code.DescriptionFits.seq {first second : Code w} (hw : 16 < 2 ^ w)
    (left : first.DescriptionFits) (right : second.DescriptionFits) : (Code.seq first second).DescriptionFits := by
  intro token member
  simp only [Code.description, List.mem_cons, List.mem_append] at member
  rcases member with rfl | member | member
  · omega
  · exact left token member
  · exact right token member

theorem Code.DescriptionFits.branch {condition : Reg} {yes no : Code w} (hw : 16 < 2 ^ w)
    (name : condition < 2 ^ w) (left : yes.DescriptionFits) (right : no.DescriptionFits) :
    (Code.branch condition yes no).DescriptionFits := by
  intro token member
  simp only [Code.description, List.mem_cons, List.mem_append] at member
  rcases member with rfl | rfl | member | member
  · omega
  · exact name
  · exact left token member
  · exact right token member

end Signatures.Runtime.CaliperBackend.WordIO
