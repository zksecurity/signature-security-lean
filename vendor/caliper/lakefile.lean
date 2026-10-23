import Lake
open Lake DSL

package caliper where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Caliper where

-- The upstream `Examples` library (executable examples and their proofs) is not declared here: its root collides with VCVio's
-- `Examples` library, which this repository imports (`Examples.Schnorr.*`).

/-- Test-only: RV64 lowering + differential-vector exporter. Not imported by
`Caliper`; users running `lake build Caliper` never build it. -/
lean_lib CaliperTest where

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"5ed2965256430c3649e86755f9576b54eca72435"
