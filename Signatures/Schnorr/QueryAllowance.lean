/-! Query allowances for Schnorr. Random calls count the attacker's requests;
the reduction also charges its own sampling and the final verification lookup. -/

namespace Schnorr

structure QueryAllowance where
  random : Nat
  hash : Nat
  sign : Nat

def QueryAllowance.total (q : QueryAllowance) : Nat := q.random + q.hash + q.sign

end Schnorr
