# Vendored Caliper source

This directory contains zkSecurity Caliper revision
`b62f7c8be35df0aa728e5a6aac7bae85eef67449`, inspected from
<https://github.com/zksecurity/caliper> on 2026-10-13.

The upstream revision targets Lean 4.32.2. This package carries only the minimal
Lean 4.34.0 port needed to preserve the same definitions and theorems:

- pin Mathlib to immutable `v4.34.0` revision
  `5ed2965256430c3649e86755f9576b54eca72435`;
- use Mathlib's new automatic `IsProbabilityMeasure (Measure.map ...)` instance;
- make the summand function explicit in one `ENNReal.le_tsum` proof.

No cost-model, execution, scoring, or resource definition was changed.
