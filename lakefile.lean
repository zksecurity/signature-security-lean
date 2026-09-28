import Lake
open Lake DSL

package «bls-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- Keep the direct VCVio pin authoritative over inherited requirements.
require Arklib from git
  "https://github.com/Verified-zkEVM/ArkLib" @
  "7653a901ed466c88a2e61a3075011b73d7bb2316"

require «agm-lean» from git
  "https://github.com/zksecurity/agm-lean" @
  "c207f29d1bba8b36fd6c09a0a3a6b4e82148b402"

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio" @
  "f5119c64ebb055d69c143704e12eba6df7dc386c"

@[default_target]
lean_lib «Signatures» where

lean_lib SignaturesTest where
  globs := #[.submodules `SignaturesTest]
  allowNonModules := true
