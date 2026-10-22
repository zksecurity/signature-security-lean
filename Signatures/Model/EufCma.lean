import Signatures.Model.RandomOracle
import VCVio.CryptoFoundations.SignatureAlg

/-! One EUF-CMA experiment for every scheme. A scheme is key generation, signing
and verification over the shared lazy random oracle (`SignatureAlg`); the
experiment and the attacker's oracle are written out below and are, by
definition, VCVio's `SignatureAlg.unforgeableExperiment` in the random-oracle
model. Each scheme's readable game is proved equal to this experiment at its
own `Scheme`. -/

open OracleComp OracleSpec

namespace Model.EufCma

variable {Input Output M PK SK S : Type} [DecidableEq Input] [SampleableType Output] [DecidableEq M]

/-- Key generation, signing and verification, all allowed to draw randomness and
hash through the shared oracle `Input → Output`. -/
abbrev Scheme (Input Output M PK SK S : Type) :=
  SignatureAlg (RandomOracle.Computation Input Output) M PK SK S

/-- Given the public key, any computation with randomness, hashing and signing
access, ending in a candidate message/signature pair. -/
abbrev Adversary (scheme : Scheme Input Output M PK SK S) := SignatureAlg.UnforgeableAdversary scheme

/-- How the attacker's requests are answered. `random` and `hash` pass through to
the shared oracle unchanged; `sign m` runs the scheme's signer under the secret
key and records the pair `(m, σ)` it returned. -/
abbrev oracle (scheme : Scheme Input Output M PK SK S) (publicKey : PK) (secretKey : SK) :
    QueryImpl (RandomOracle.Spec Input Output + (M →ₒ S))
      (WriterT (QueryLog (M →ₒ S)) (RandomOracle.Computation Input Output)) :=
  (RandomOracle.Spec Input Output).passthrough + scheme.signingOracle publicKey secretKey

/-- Generate a key pair, run the attacker against the oracle, verify its forgery
and require the forged message never to have been signed. Key generation, the
oracle and verification share one initially empty lazy random oracle. -/
noncomputable def game {scheme : Scheme Input Output M PK SK S} (adversary : Adversary scheme) :
    ProbComp Bool :=
  RandomOracle.run (SignatureAlg.unforgeableExperiment adversary)

/-- The experiment, written out. -/
theorem game_eq {scheme : Scheme Input Output M PK SK S} (adversary : Adversary scheme) :
    game adversary = RandomOracle.run (do
    let (publicKey, secretKey) ← scheme.keygen
    let ((message, signature), signingLog) ←
      (simulateQ (oracle scheme publicKey secretKey) (adversary.main publicKey)).run
    let valid ← scheme.verify publicKey message signature
    return !signingLog.wasQueried message && valid) := by
  simp only [game, SignatureAlg.unforgeableExperiment, SignatureAlg.runWithSigningOracle_def, oracle]
  congr!

end Model.EufCma
