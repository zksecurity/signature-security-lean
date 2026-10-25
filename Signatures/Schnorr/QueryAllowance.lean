import Signatures.Model.QueryAllowance
/-! Query allowances for Schnorr. Random calls count the attacker's requests;
the reduction also charges its own sampling and the final verification lookup. -/

namespace Schnorr

/-- The shared allowance, see `Model.QueryAllowance`. -/
abbrev QueryAllowance := Model.QueryAllowance

abbrev QueryAllowance.total (q : QueryAllowance) : Nat := Model.QueryAllowance.total q

end Schnorr
