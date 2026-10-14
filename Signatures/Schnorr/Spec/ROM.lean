import Examples.Schnorr.Signature

/-!
# Schnorr source game

Reuse VCVio's Schnorr algorithms and adaptive EUF-CMA adversary unchanged. The hash oracle
takes a message/commitment pair and returns a scalar. Signing, adversary hash queries, and
final verification share one lazy cache. This is ordinary ROM security, without AGM evidence.
The public endpoint combines this game with a certified two-pass replay machine.
-/

open OracleComp OracleSpec

namespace Schnorr.ROM

variable {F G M : Type} [Field F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] [DecidableEq M]

/-- Public randomness, scalar-valued hash queries, and signing queries, respectively. -/
abbrev advSpec (F G M : Type) := (unifSpec + (M × G →ₒ F)) + (M →ₒ G × F)

/-- No algebraicity or fixed query schedule is required. -/
abbrev Adversary (g : G) := SignatureAlg.UnforgeableAdversary (Schnorr.signature F G g M)

/-- Key generation, adaptive interaction, signature verification, and message freshness,
all under a single initially empty lazy random-oracle cache. -/
noncomputable def game (g : G) (A : Adversary (F := F) (M := M) g) : ProbComp Bool := by
  classical
  letI : DecidableEq (M × G) := Classical.decEq _
  exact (simulateQ (M × G →ₒ F).romImpl (SignatureAlg.unforgeableExperiment A)).run' ∅

theorem game_eq_advantage (g : G) (A : Adversary (F := F) (M := M) g) :
    𝒟[game g A] {true} =
      SignatureAlg.unforgeableAdvantage (FiatShamir.runtime (Commit := G) (Chal := F) M) A := by
  rw [SignatureAlg.unforgeableAdvantage, FiatShamir.runtime_eq_runtimeWithCache_empty,
    FiatShamir.runtimeWithCache_evalDist]
  unfold game
  congr!

end Schnorr.ROM
