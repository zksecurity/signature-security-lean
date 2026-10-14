import Signatures.BLS.Statement

/-! Compatibility names for the former AGM-only interface. The two public
statements are in `Statement.lean`; their definitions are in
`GeneralSecurityModel.lean` and their proofs in `Proofs/GeneralSecurity.lean`. -/

namespace BLS

-- Preserve the original independent backend universes in this type alias.
set_option linter.checkUnivs false in
/-- Compatibility name for the AGM-only model. New callers should select
`AGMSecurityModel` or `CoCDHSecurityModel` explicitly. -/
abbrev SecurityModel := AGMSecurityModel

/-- Compatibility name for the AGM-to-DLog theorem. -/
alias security := agm_security

/-- Compatibility name for the AGM game. -/
noncomputable abbrev eufCmaGame := agmEufCmaGame

alias eufCmaGame_eq := agmEufCmaGame_eq

variable (curve : Model.PairingCurve) [model : SecurityModel curve]

/-- Compatibility name for DLog success at the derived good-branch budget. -/
noncomputable def goodDLogBound (securityParameter : Nat) (queries : QueryAllowance) : ENNReal :=
  dlogSuccessBound curve securityParameter queries (model.parameters securityParameter queries).goodTime

/-- Compatibility name for DLog success at the derived bad-branch budget. -/
noncomputable def badDLogBound (securityParameter : Nat) (queries : QueryAllowance) : ENNReal :=
  dlogSuccessBound curve securityParameter queries (model.parameters securityParameter queries).badTime

end BLS
