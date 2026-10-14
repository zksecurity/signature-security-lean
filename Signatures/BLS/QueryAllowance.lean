/-! Query allowances shared by the BLS AGM and unrestricted co-CDH routes. -/

namespace BLS

structure QueryAllowance where
  random : Nat
  hash : Nat
  sign : Nat

def QueryAllowance.total (q : QueryAllowance) : Nat := q.random + q.hash + q.sign

def queryKind {HashInput SignInput : Type} : (Nat ⊕ HashInput) ⊕ SignInput → Fin 3
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 2

end BLS
