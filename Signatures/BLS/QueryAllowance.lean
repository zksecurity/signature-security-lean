import Signatures.Model.QueryAllowance
/-! Query allowances shared by the BLS AGM and unrestricted co-CDH routes. -/

namespace BLS

/-- The shared allowance, see `Model.QueryAllowance`. -/
abbrev QueryAllowance := Model.QueryAllowance

abbrev QueryAllowance.total (q : QueryAllowance) : Nat := Model.QueryAllowance.total q

def queryKind {HashInput SignInput : Type} : (Nat ⊕ HashInput) ⊕ SignInput → Fin 3
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 2

end BLS
