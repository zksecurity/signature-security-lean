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

-- Caliper on its `lean-4.36` branch; a local checkout until that branch is published.
require caliper from "../../caliper"

@[default_target]
lean_lib «Signatures» where

@[default_target]
lean_lib Proofs where

lean_lib SignaturesTest where
  globs := #[.submodules `SignaturesTest]
  allowNonModules := true
