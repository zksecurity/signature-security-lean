import Signatures.Schnorr.Spec.ROM

/-!
Internal probability theorem for the Schnorr route. The public machine-bounded
endpoint is in `Signatures.Schnorr.Statement`.

The reduction simulates signatures by sampling `c,z`, constructing `R = z*g - c*pk`,
and programming `H(m,R) = c`; programming collisions account for the subtraction below.
The upstream replay selects a fresh challenge occurrence, retains its prefix, and
independently completes that occurrence again. The two accepting transcripts must
select the same occurrence and have distinct challenges before extraction.

`qH` bounds adversary hash calls and `qS` bounds signing calls, on every reply path.
The extra hash slot covers the final forgery's verification challenge. Neither bound
limits adversary randomness or pure computation. `ReplayForkCost` bounds oracle calls
by twice the original bound, not machine time.

`Runtime.SchnorrForkBudget` charges the complete two-pass machine, including replay,
cache scans, verification, extraction, fallback, and loading fixed data. Rewinding
re-executes the source from its root with a recorded prefix; no free continuation
snapshot is assumed. `SchnorrSource` and `SchnorrTrace` identify its expanded adaptive
interpreter with `Fork.runTrace`, including the final live query. `SchnorrReduction`
proves exact equality to `dlogReduction` and derives its machine certificate from
the original adversary's source budget. Private scalar sampling may expand into
multiple primitive uniform queries without changing the joint fork distribution.
-/

open OracleComp DiffieHellman

namespace Schnorr.ROM.Proofs

variable {F G M : Type} [Field F] [SampleableType F] [Fintype F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] [DecidableEq M]

/-- Signing simulation loses at most `qS * (qS + qH) / |F|`. The remaining success feeds
the forking bound, with one extra hash slot for the final forgery. Subtraction is truncated
at zero in ENNReal. Query bounds hold on every reply path and for every public key. -/
theorem security (g : G) (hgen : Function.Bijective (fun x : F => x • g))
    (A : Adversary (F := F) (M := M) g) (qS qH : Nat)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound (M := M) (oa := A.main pk) qS qH) :
    let eps := 𝒟[game g A] {true} -
      (qS : ENNReal) * (qS + qH) * (Fintype.card F : ENNReal)⁻¹
    eps * (eps / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      𝒟[dlogExperiment g (Schnorr.dlogReduction F G g M A qH)] {true} := by
  rw [game_eq_advantage]
  simpa only [FiatShamir.challengeSpaceInv, evalDist_apply_singleton] using
    Schnorr.signature_euf_cma F G g hgen M A qS qH hQ

end Schnorr.ROM.Proofs
