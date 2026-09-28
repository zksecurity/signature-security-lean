/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Mathlib.Algebra.Module.Basic

/-!
# Abstract (type-3) bilinear pairings

`mathlib` formalises the elliptic-curve group law (`WeierstrassCurve`) but not the Weil/Tate
pairing, so for pairing-based signatures we axiomatise the structure a security proof actually
uses: a bilinear, nondegenerate map `e : G₁ × G₂ → Gₜ`.  This is the standard abstract-bilinear-
group model (type-3, `G₁ ≠ G₂`, no efficient isomorphism between them).
-/

namespace AlgebraicGroupModel

/-- An abstract bilinear pairing `e : G₁ × G₂ → Gₜ` over scalar field `F`. -/
class BilinearPairing (F G₁ G₂ Gₜ : Type) [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] where
  /-- the pairing operation, written `e x y` (textbook `⟨x, y⟩`). -/
  e : G₁ → G₂ → Gₜ
  e_smul_left  (a : F) (x : G₁) (y : G₂) : e (a • x) y = a • e x y
  e_smul_right (a : F) (x : G₁) (y : G₂) : e x (a • y) = a • e x y
  e_add_left   (x x' : G₁) (y : G₂) : e (x + x') y = e x y + e x' y
  e_add_right  (x : G₁) (y y' : G₂) : e x (y + y') = e x y + e x y'

/-- The pairing `e x y`, with type/instance arguments implicit.  Prefer this over the raw class
projection `BilinearPairing.e` (whose carrier types are explicit). -/
def pairing {F G₁ G₂ Gₜ : Type} [Field F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [inst : BilinearPairing F G₁ G₂ Gₜ] (x : G₁) (y : G₂) : Gₜ := inst.e x y

section lemmas
variable {F G₁ G₂ Gₜ : Type} [Field F] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [inst : BilinearPairing F G₁ G₂ Gₜ]

@[simp] theorem pairing_smul_left (a : F) (x : G₁) (y : G₂) :
    pairing (F := F) (a • x) y = a • (pairing (F := F) x y : Gₜ) := inst.e_smul_left a x y

@[simp] theorem pairing_smul_right (a : F) (x : G₁) (y : G₂) :
    pairing (F := F) x (a • y) = a • (pairing (F := F) x y : Gₜ) := inst.e_smul_right a x y

@[simp] theorem pairing_add_left (x x' : G₁) (y : G₂) :
    pairing (F := F) (x + x') y = pairing (F := F) x y + (pairing (F := F) x' y : Gₜ) :=
  inst.e_add_left x x' y

@[simp] theorem pairing_add_right (x : G₁) (y y' : G₂) :
    pairing (F := F) x (y + y') = pairing (F := F) x y + (pairing (F := F) x y' : Gₜ) :=
  inst.e_add_right x y y'

end lemmas

end AlgebraicGroupModel
