import Signatures.Schnorr.Spec.ROM
import Proofs.Runtime.SeededLazyFork
import VCVio.CryptoFoundations.FiatShamir.Sigma.Reductions

/-! The ordinary Schnorr ROM reduction with encountered randomness retained
for replay. Its program takes neither a family cover nor an eager seed budget.
Probability correspondence and security are proved in separate files; native
execution and encoded-memory bounds require additional implementation work. -/

open OracleComp OracleSpec DiffieHellman

namespace Schnorr.LazyROM

variable {F A : Type} [SampleableType F] [DecidableEq F]

/-- No family cover or private-query budget is used by the lazy controller. -/
def fork (main : OracleComp (unifSpec + (Unit →ₒ F)) A) (qH : Nat)
    (select : A → Option (Fin (qH + 1))) :
    OracleComp (unifSpec + (Unit →ₒ F)) (Option (A × A)) :=
  Signatures.Runtime.SeededLazyFork.recordedFork main (.inr ()) select

/-- Interpret private draws directly and fresh hash challenges by uniform
scalar sampling, after the retained-tape fork has been formed. -/
def sample : QueryImpl (unifSpec + (Unit →ₒ F)) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp + uniformSampleImpl (spec := Unit →ₒ F)

variable {G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [SampleableType G] [DecidableEq G] [DecidableEq M]

/-- Simulate signing and record the verification hash lookup as in the
established Schnorr source experiment. -/
abbrev main (g pk : G) (adv : ROM.Adversary (F := F) (M := M) g) :=
  FiatShamir.Fork.runTrace (Schnorr.sigma F G g) (dlogGenerable F g) M
    (FiatShamir.cmaToNmaAdv (Schnorr.sigma F G g) (dlogGenerable F g) M
      (Schnorr.simTranscript F G g) adv) pk

/-- Replay with the retained private randomness, change the selected challenge,
then apply the existing special-soundness extractor. Only actual encountered
draws are recorded; proof-only seed covers are absent from this construction. -/
def dlogReduction (g : G) (adv : ROM.Adversary (F := F) (M := M) g)
    (qH : Nat) : DLogAdversary F G := fun _ pk =>
  simulateQ sample (fork (main g pk adv) qH (FiatShamir.Fork.forkPoint G F F M qH) >>=
    FiatShamir.nmaForkExtractBranch (M := M) (Schnorr.sigma F G g))

end Schnorr.LazyROM
