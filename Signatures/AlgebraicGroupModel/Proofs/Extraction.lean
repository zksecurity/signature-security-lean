/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Mathlib.Tactic.LinearCombination
import Signatures.AlgebraicGroupModel.Spec.AffineForm

/-!
# Algebraic Group Model — secret-key extraction (field-algebra core)

In an AGM reduction, every group element the adversary sees has a discrete log that is a known
affine function of the single secret `α`: `dlog = const + lin·α`.  An algebraic forgery's dlog is
again such a form `out`, and the verification equation forces `out.eval α = c·α` for a known
target `c`.  As soon as `out.lin ≠ c`, the secret is read off: `α = out.const / (c − out.lin)`.

This is the tool-agnostic heart of pairing-based AGM signature reductions; it is ported verbatim
from the standalone `Agm` development.
-/

namespace AlgebraicGroupModel

variable {F : Type*} [Field F]

/-- **AGM secret extraction.**  If the forgery's dlog `out.eval α` equals `c·α` and its
`α`-coefficient differs from `c`, the secret is `α = out.const / (c − out.lin)`. -/
theorem extract_secret {α c : F} {out : AffineForm F}
    (hverify : out.eval α = c * α) (hnondeg : out.lin ≠ c) :
    α = out.const / (c - out.lin) := by
  have hc : c - out.lin ≠ 0 := sub_ne_zero.mpr hnondeg.symm
  rw [eq_div_iff hc]
  simp only [AffineForm.eval] at hverify
  linear_combination -hverify

end AlgebraicGroupModel
