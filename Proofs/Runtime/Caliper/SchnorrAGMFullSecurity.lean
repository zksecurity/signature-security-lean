import Proofs.Runtime.Caliper.SchnorrAGMFullDLog
import Proofs.Runtime.SchnorrAGMSecurity

/-! The concrete Schnorr AGM route: `SchnorrAGM.security` bounds the forgery by the
named reduction's DLog success, and `dlogWithin` places that reduction in the
fixed Caliper class at the derived code, time and total-memory budgets. -/
