import Proofs.Model.LazyAGM

/-! # Degree-bounded OOPS with lazily sampled topic/degree bases

This is the oracle-derived-base variant, not a replacement for public setup parameters.
-/

namespace OOPS.LazyAGM

-- Concrete oracles: hash(topic,j) returns H(topic,j), with j in 0,...,d;
-- sign(m,topic) returns alpha * sum_{j=0}^d m^j * H(topic,j).
-- Model.LazyAGM.signing implements this sum using the shared cache supplied by lazyImpl.
-- Model.LazyAGM.Interactive.impl dispatches queries; experiment generates the key and checks
-- the pairing equation, pair freshness, and admissible. No per-query degree is chosen.
-- Fix degree d; mt contains a scalar message and a topic. Each base has a topic/degree index.
def terms {F T : Type} [Monoid F] (d : Nat) (mt : F × T) : List ((T × Fin (d + 1)) × F) :=
  -- Enumerate j = 0,...,d: the base for (topic,j) receives weight message^j.
  List.ofFn fun j : Fin (d + 1) => ((mt.2, j), mt.1 ^ (j : Nat))

@[simp] theorem terms_length {F T : Type} [Monoid F] (d : Nat) (mt : F × T) :
    (terms d mt).length = d + 1 := by simp [terms]

-- Equality lets the winning predicate select a topic and remove repeated scalar messages.
def admissible {F T : Type} [DecidableEq F] [DecidableEq T]
    -- Compare the eventual forged pair mt against the actual signed-pair transcript.
    (d : Nat) (mt : F × T) (signed : List (F × T)) : Prop :=
  -- Count distinct messages only on the forged topic; repeats and other topics add no count.
  ((signed.filter fun q => q.2 = mt.2).map Prod.fst).toFinset.card ≤ d

instance {F T : Type} [DecidableEq F] [DecidableEq T] (d : Nat) (mt : F × T) (signed : List (F × T)) :
    Decidable (admissible d mt signed) := by
  unfold admissible
  infer_instance

-- The game is parameterized by scalars, topics, source groups, and a pairing target group.
noncomputable def game {F T G₁ G₂ Gₜ : Type}
    -- Sample scalars uniformly; topic equality supports base caching and topic selection.
    [Field F] [SampleableType F] [DecidableEq T]
    -- Lazily sampled polynomial bases and signatures are G1 points with F-scalar actions.
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    -- G2 holds verification keys and Gt holds pairing values, both with F-scalar actions.
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    -- The verifier uses this pairing; security theorems separately require nondegeneracy.
    [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]
    -- Degree d is fixed for the whole game, not chosen separately in each signing query.
    (g₁ : G₁) (g₂ : G₂) (d : Nat)
    -- A hashes topic/degree indices, signs scalar/topic pairs, and returns an algebraic forgery.
    (A : Model.LazyAGM.Adversary F (T × Fin (d + 1)) (F × T) G₁ G₂) : ProbComp Bool := by
  -- Supply classical scalar equality for the mathematical distinct-message winning check.
  classical
  -- Use polynomial weights and require at most d distinct signed messages on the target topic.
  exact Model.LazyAGM.game (Gₜ := Gₜ) (terms d) (admissible d) g₁ g₂ A

/-- Scalar equality only counts distinct signed messages in the winning condition.
Any supplied decider gives exactly the same game as classical equality. -/
theorem game_eq_of_decidableEq {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [DecidableEq F] [DecidableEq T]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]
    (g₁ : G₁) (g₂ : G₂) (d : Nat)
    (A : Model.LazyAGM.Adversary F (T × Fin (d + 1)) (F × T) G₁ G₂) :
    game (Gₜ := Gₜ) g₁ g₂ d A =
      Model.LazyAGM.game (Gₜ := Gₜ) (terms d) (admissible d) g₁ g₂ A := by
  unfold game
  congr 2
  exact Subsingleton.elim _ _

end OOPS.LazyAGM
