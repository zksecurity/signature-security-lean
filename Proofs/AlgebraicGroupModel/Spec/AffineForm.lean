/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Mathlib.Algebra.Field.Basic

/-!
# Algebraic Group Model — the affine-form representation (spec)

In an AGM reduction, every group element the adversary sees has a discrete log that is a known
affine function of the single secret `α`: `dlog = const + lin·α`.  `AffineForm` is that shape;
`eval` realises it at a concrete secret.  The extraction lemma lives in
`Signatures.AlgebraicGroupModel.Proofs.Extraction`.
-/

namespace AlgebraicGroupModel

variable {F : Type*} [Field F]

/-- A discrete log viewed as an affine function of the secret `α`: `eval = const + lin·α`. -/
@[ext]
structure AffineForm (F : Type*) where
  /-- the `α`-free part of the discrete log. -/
  const : F
  /-- the coefficient of the secret `α`. -/
  lin : F

namespace AffineForm

/-- Realise the form at a concrete secret `α`. -/
def eval (s : AffineForm F) (α : F) : F := s.const + s.lin * α

end AffineForm

end AlgebraicGroupModel
