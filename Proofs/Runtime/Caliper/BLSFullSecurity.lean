import Proofs.Runtime.Caliper.BLSFullDLog
import Proofs.BLS.LazyAGMArbitraryMessages
import Proofs.Model.DirectAGM

/-! The two ingredients of concrete BLS AGM security against the fixed Caliper
DLog class: the full reduction certificates `BLSFull.good_dlogWithin` and
`BLSFull.bad_dlogWithin`, built from named primitive implementations and local
caller code, and the probability reduction
`BLS.LazyAGM.Reduction.security_arbitrary_messages_list`. The public route
combines them in `Proofs/BLS/GeneralSecurity.lean`. -/
