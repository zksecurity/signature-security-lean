import Signatures.BLS.Statement

/-! Compatibility names for the former AGM-only interface. The two public
statements are in `Statement.lean`; their definitions are in
`GeneralSecurityModel.lean` and their proofs in `Proofs/GeneralSecurity.lean`. -/

namespace BLS

/-- Compatibility name for the AGM-only model. New callers should select
`AGMSecurityModel` or `CoCDHSecurityModel` explicitly. -/
abbrev SecurityModel := AGMSecurityModel

/-- Compatibility name for the AGM-to-DLog theorem. -/
alias security := Proofs.agm_security

/-- Compatibility name for the AGM game. -/
noncomputable abbrev eufCmaGame := agmEufCmaGame

alias eufCmaGame_eq := agmEufCmaGame_eq

end BLS
