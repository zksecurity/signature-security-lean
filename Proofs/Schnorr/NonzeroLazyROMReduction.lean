import Signatures.Schnorr.Spec.NonzeroNonce
import Proofs.Schnorr.LazyFiatShamirReduction

/-! Nonzero-nonce Schnorr with lazy retained-private-tape replay. The signing
simulator is the exact finite repair sampler from the separate source scheme;
the full-field simulator is not substituted for it. -/

open OracleComp OracleSpec DiffieHellman

namespace Schnorr.NonzeroNonce.LazyROM

variable {F G M : Type} [Field F] [SampleableType F] [SampleableType Fˣ] [DecidableEq F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] [DecidableEq M]

abbrev main (g pk : G) (adv : Adversary (F := F) (M := M) g) :=
  FiatShamir.LazyTape.main (sigma g) (dlogGenerable F g) M (simTranscript g) adv pk

/-- Record only encountered random draws, retain the private tape across both
runs, change the selected challenge, then extract or return the usual fallback. -/
def dlogReduction (g : G) (adv : Adversary (F := F) (M := M) g) (qH : Nat) :
    DLogAdversary F G := fun _ pk =>
  FiatShamir.LazyTape.reduction (sigma g) (dlogGenerable F g) M (simTranscript g) adv qH pk

end Schnorr.NonzeroNonce.LazyROM
