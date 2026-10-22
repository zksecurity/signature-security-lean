import Signatures.BLS.Proofs.GeneralSecurity
import Signatures.BLS.CaliperAGMFamilyStatement
import Signatures.BLS.CaliperCoCDHFamilyStatement
import Signatures.BLS.CaliperCoCDHCaller
import Signatures.BLS.ArithmeticStatement

/-! BLS security. Fix the curve, security parameter, query allowances and
execution model, then quantify over the attacker. `Game.lean` contains the game
without machine contracts. Proofs and derived budgets stay in supporting files.

Below, `p` is the group order and `εDL` is the DLog success bound at the proved
reduction budget, in the same execution model. A hardness assumption makes it
small. The notation expands to the existing resource-indexed quantities.
-/

namespace BLS

section AGM

variable (curve : Model.PairingCurve) [AGMSecurityModel curve]
  (securityParameter : Nat) (queries : QueryAllowance)

local notation "p" => (curve.order securityParameter : ENNReal)
local notation "εDL" => dlogSuccessBound curve securityParameter queries (agmReductionTime curve securityParameter queries)
local notation "EUFCMA" => agmEufCmaGame curve securityParameter

/-- Every resource-bounded algebraic attacker satisfies this forgery bound. -/
theorem agm_security
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    𝒟[EUFCMA adversary] {true} ≤ 2 * εDL + 1 / p :=
  Proofs.agm_security_common_budget curve securityParameter queries adversary

end AGM

section CoCDH

variable (curve : Model.PairingCurve) [CoCDHSecurityModel curve]
  (securityParameter : Nat) (queries : QueryAllowance)

-- The Coron factor depends only on signing calls; at zero calls it is one.
-- εcoCDH uses the complete proved Coron reduction budget in the same model.
local notation "εcoCDH" => coCDHSuccessBound curve securityParameter queries
  (cocdhReductionTime curve securityParameter queries)
local notation "EUFCMA" => cocdhEufCmaGame curve securityParameter

/-- Every resource-bounded unrestricted attacker satisfies this ROM bound. -/
theorem cocdh_security
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    𝒟[EUFCMA adversary] {true} ≤ Model.coronFactor queries.sign * εcoCDH :=
  Proofs.cocdh_security curve securityParameter queries adversary

end CoCDH

end BLS
