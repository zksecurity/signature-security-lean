import Signatures.BLS.Statement

/-! Compatibility import. The public model, game, success bound, and theorem now
live together in `Statement.lean`, so their meaning can be read in one place. -/

namespace BLS

variable (curve : Model.PairingCurve) [model : SecurityModel curve]

/-- Compatibility name for DLog success at the derived good-branch budget. -/
noncomputable def goodDLogBound (securityParameter : Nat) (queries : QueryAllowance) : ENNReal :=
  dlogSuccessBound curve securityParameter queries (model.parameters securityParameter queries).goodTime

/-- Compatibility name for DLog success at the derived bad-branch budget. -/
noncomputable def badDLogBound (securityParameter : Nat) (queries : QueryAllowance) : ENNReal :=
  dlogSuccessBound curve securityParameter queries (model.parameters securityParameter queries).badTime

end BLS
