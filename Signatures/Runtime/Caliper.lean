import Signatures.Runtime.Caliper.Program
import Signatures.Runtime.Caliper.Encoding
import Signatures.Runtime.Caliper.Crypto
import Signatures.Runtime.Caliper.Routine
import Signatures.Runtime.Caliper.Hoare
import Signatures.Runtime.Caliper.Realizer
import Signatures.Runtime.Caliper.Resources
import Signatures.Runtime.Caliper.Words
import Signatures.Runtime.Caliper.Memory

/-! Caliper execution and separately certified encoded cryptographic routines.
This module is independent of the signature games. It supplies a concrete local
quantitative backend and charged copying; it does not yet instantiate the full
signature security models or their oracle/replay controllers.
-/
