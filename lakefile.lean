import Lake
open Lake DSL

package «bls-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio" @
  "70c422d63c07fd3401dd85c51e8b3ed8fd587718"

-- Caliper on the `lean-4.36` branch (zksecurity/caliper#2), from the fork until it merges.
require caliper from git
  "https://github.com/kobizk/caliper" @
  "1d9c510fa1f42d8f2aa040fd5c7a979f857ca2fe"

@[default_target]
lean_lib «Signatures» where

@[default_target]
lean_lib Proofs where

lean_lib SignaturesTest where
  globs := #[.submodules `SignaturesTest]
  allowNonModules := true
