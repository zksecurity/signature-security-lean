import Proofs.Model.LazyAGM

/-! # Proximity with lazily sampled slot/coordinate bases

The source game checks ordinary freshness and validity. Fresh linear collisions are measured
separately and contribute their actual probability to the security bound, not a rejection rule.
This is an oracle-derived-base variant, not a replacement for public setup parameters.
-/

namespace Proximity.LazyAGM

open OracleComp

-- Concrete oracles: hash(coordinate,slot) returns that slot's constant or coordinate base;
-- sign(m,slot) returns alpha * (H(none,slot) + sum_k m[k] * H(some k,slot)).
-- Model.LazyAGM.signing implements this sum using the shared cache supplied by lazyImpl.
-- Model.LazyAGM.Interactive.impl dispatches queries; experiment generates the key and checks
-- the pairing equation and vector/slot freshness. Collisions are not an oracle restriction.
-- ms contains an ell-coordinate scalar vector and a slot; F supplies the constant weight one.
def terms {F S : Type} [One F] {ℓ : Nat} (ms : (Fin ℓ → F) × S) :
    -- Each weighted base is indexed by an optional coordinate and a slot.
    List ((Option (Fin ℓ) × S) × F) :=
  -- none selects the constant base; some k selects coordinate k, weighted by that message entry.
  ((none, ms.2), 1) :: List.ofFn (fun k : Fin ℓ => ((some k, ms.2), ms.1 k))

@[simp] theorem terms_length {F S : Type} [One F] {ℓ : Nat} (ms : (Fin ℓ → F) × S) :
    (terms ms).length = ℓ + 1 := by simp [terms]

/-- A fresh output whose vector equals the signing-coefficient-weighted sum of signed vectors.
All signed messages contribute, including repeats and messages from other slots.
This event does not require the output signature to verify. -/
def Collision {F S : Type} [Semiring F] {ℓ : Nat}
    -- Read the target and coefficients from the adversary's output, and messages from the log.
    (out : Model.LazyAGM.Output F ((Fin ℓ → F) × S)) (signed : List ((Fin ℓ → F) × S)) : Prop :=
  -- Freshness concerns the full vector/slot pair.
  out.mstar ∉ signed ∧
    -- Missing coefficients count as zero, exactly as in signature materialization.
    out.mstar.1 = fun k => (signed.mapIdx fun n m =>
      Model.LazyAGM.tokenCoeff out.ξ n * m.1 k).sum

section Game

-- Fix scalar/slot/group types and vector length; ell is shared by all messages in this game.
variable {F S G₁ G₂ Gₜ : Type} {ℓ : Nat}
  -- Sample scalars uniformly; slot equality is used for persistent base-cache lookup.
  [Field F] [SampleableType F] [DecidableEq S]
  -- G1 contains the uniformly sampled bases and the resulting signature points.
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  -- G2 contains verification keys; Gt contains pairing values; both support F-scalars.
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  -- The verifier is parameterized by this bilinear pairing.
  [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]

-- Fix the signature-group generator input and verification-key base point.
noncomputable def game (g₁ : G₁) (g₂ : G₂)
    -- Hash requests select coordinate/slot bases; signing requests contain a vector/slot pair.
    (A : Model.LazyAGM.Adversary F (Option (Fin ℓ) × S) ((Fin ℓ → F) × S) G₁ G₂) :
    -- The probabilistic computation returns true exactly when the winning check accepts.
    ProbComp Bool :=
  -- No extra admissibility test: validity and full vector/slot freshness determine success.
  Model.LazyAGM.game (Gₜ := Gₜ) terms (fun _ _ => True) g₁ g₂ A

/-- Observe fresh collisions in the same key generation and adaptive interaction as game.
The grouped runner is exactly related to certified execution by interactiveRun_eq. -/
noncomputable def collisionExperiment (g₂ : G₂)
    (A : Model.LazyAGM.Adversary F (Option (Fin ℓ) × S) ((Fin ℓ → F) × S) G₁ G₂) :
    OracleComp (Model.LazyAGM.baseSpec (Option (Fin ℓ) × S) G₁) Bool := by
  classical
  exact do
    -- Sample the same secret-key distribution, including zero.
    let α ← liftM ($ᵗ F)
    -- Keep the exact adaptive signer and hash interface; do not condition on noncollision.
    let (out, tr) ← Model.LazyAGM.run terms α A (α • g₂)
    -- Observe the transcript event without changing the original winning check.
    pure (decide (Collision out (tr.2.map Prod.fst)))

/-- Probability experiment for the collision term, using the source game's lazy hash cache. -/
noncomputable def collisionGame (g₂ : G₂)
    (A : Model.LazyAGM.Adversary F (Option (Fin ℓ) × S) ((Fin ℓ → F) × S) G₁ G₂) : ProbComp Bool :=
  -- Hashing and internal signing lookups share one initially empty cache.
  (simulateQ Model.LazyAGM.lazyImpl (collisionExperiment g₂ A)).run' ∅

end Game

end Proximity.LazyAGM
