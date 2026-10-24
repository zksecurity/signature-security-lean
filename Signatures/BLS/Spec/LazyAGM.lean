import Proofs.Model.LazyAGM

/-! # BLS with query-only random-oracle access and an algebraic output -/

namespace BLS.LazyAGM

-- Concrete oracles: hash(m) returns H(m); sign(m) returns alpha * H(m).
-- Model.LazyAGM.signing implements the signer and lazyImpl supplies the shared hash cache.
-- Model.LazyAGM.experiment generates the key and checks the final forgery;
-- Model.LazyAGM.Interactive.impl dispatches randomness, hash, and signing queries.
-- BLS signs one hash point: use the message itself as its base index, with weight one.
def terms {F M : Type} [One F] (m : M) : List (M × F) := [(m, 1)]

-- F is the scalar field, M the message type, and G1/G2/Gt the two source groups and target.
noncomputable def game {F M G₁ G₂ Gₜ : Type}
    -- Sample secret scalars uniformly; message equality supports caching and freshness.
    [Field F] [SampleableType F] [DecidableEq M]
    -- Signatures and uniformly sampled hash points live in the additive F-module G1.
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    -- Verification keys live in G2; pairing results live in Gt. Both support F-scalars.
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    -- Supply a bilinear pairing; generator and nondegeneracy premises belong to the theorems.
    [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]
    -- Fix the two base points and A; both hash indices and signed messages have type M.
    (g₁ : G₁) (g₂ : G₂) (A : Model.LazyAGM.Adversary F M M G₁ G₂) : ProbComp Bool :=
  -- Run the shared lazy game. True adds no extra condition beyond validity and freshness.
  Model.LazyAGM.game (Gₜ := Gₜ) terms (fun _ _ => True) g₁ g₂ A

end BLS.LazyAGM
