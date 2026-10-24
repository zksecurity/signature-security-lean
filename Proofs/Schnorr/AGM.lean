import Signatures.Schnorr.Spec.ROM
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
The straight-line extraction equations for Schnorr in the AGM+ROM.
Representations must be recorded when a fresh hash query is made, before its
challenge is sampled. An explanation chosen after seeing that challenge does
not justify the bad-challenge probability bound.

These are algebraic lemmas, not an adaptive EUF-CMA probability theorem.
-/

namespace Schnorr.AGM

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-- A representation flattened over the initial generator and public key. -/
structure Affine (F : Type) where
  constant : F
  secret : F

def Affine.eval (a : Affine F) (g pk : G) : G :=
  a.constant • g + a.secret • pk

/-- A simulated signing reply has a known affine representation without knowing the secret. -/
def signingRepresentation (c z : F) : Affine F := ⟨z, -c⟩

theorem signingRepresentation_eval (g pk : G) (c z : F) :
    (signingRepresentation c z).eval g pk = z • g - c • pk := by
  simp [signingRepresentation, Affine.eval, sub_eq_add_neg]

/-- Compose explanations of received signing commitments back to the two initial inputs. -/
def combine (terms : List (F × Affine F)) : Affine F :=
  ⟨(terms.map fun p => p.1 * p.2.constant).sum,
    (terms.map fun p => p.1 * p.2.secret).sum⟩

theorem combine_eval (terms : List (F × Affine F)) (g pk : G) :
    (combine terms).eval g pk = (terms.map fun p => p.1 • p.2.eval g pk).sum := by
  induction terms with
  | nil => simp [combine, Affine.eval]
  | cons p terms ih =>
      simp only [combine, List.map_cons, List.sum_cons, Affine.eval] at ih ⊢
      rw [add_smul, add_smul, smul_add, ← mul_smul, ← mul_smul, ← ih]
      abel

/-- One accepting signature extracts the discrete logarithm unless its denominator vanishes. -/
theorem extract (g : G) (hg : Function.Injective (fun x : F => x • g))
    (x c z : F) (a : Affine F)
    (hv : z • g = a.eval g (x • g) + c • (x • g))
    (hne : a.secret + c ≠ 0) :
    (z - a.constant) / (a.secret + c) = x := by
  have hz : z = a.constant + (a.secret + c) * x := hg (by
    simpa [Affine.eval, add_smul, mul_smul, add_assoc] using hv)
  apply (div_eq_iff hne).2
  rw [hz]
  ring

/-- For a coefficient fixed before the challenge, precisely one challenge is exceptional. -/
theorem bad_challenge_iff (a : Affine F) (c : F) :
    a.secret + c = 0 ↔ c = -a.secret := by
  constructor <;> intro h <;> linear_combination h

/-- This is conditional on a fixed pre-query representation, not a post-query choice. -/
theorem bad_challenge_probability [SampleableType F] [Fintype F] (a : Affine F) :
    Pr{let c ← $ᵗ F}[a.secret + c = 0] = (Fintype.card F : ENNReal)⁻¹ := by
  simp only [bad_challenge_iff]
  exact SampleableType.prEvent_uniformSample_eq_singleton (-a.secret)

end Schnorr.AGM
