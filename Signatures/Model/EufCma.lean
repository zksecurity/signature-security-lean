import Signatures.Model.RandomOracle
import VCVio.CryptoFoundations.SignatureAlg

/-! One EUF-CMA experiment for every scheme and every attacker model. A scheme is
key generation, signing and verification over the shared lazy random oracle
(`SignatureAlg`). An attacker model says how an attacker is run against the
signing oracle; it reports the forgery with the messages it had signed and
whether it respected the model's protocol, or nothing when it produced no
checkable forgery. Ordinary attackers are oracle programs and always respect it;
algebraic attackers additionally explain every group element they output, and a
malformed interaction loses. A scheme may restrict winning forgeries further
(`admissible`, e.g. OOPS's degree rule); by default it does not. For ordinary
attackers the experiment is VCVio's `SignatureAlg.unforgeableExperiment` in the
random-oracle model (`game_eq_unforgeableExperiment`). -/

open OracleComp OracleSpec

namespace Model.EufCma

variable {Input Output M PK SK S : Type} [DecidableEq Input] [SampleableType Output] [DecidableEq M]

/-- Key generation, signing and verification, all allowed to draw randomness and
hash through the shared oracle `Input → Output`. -/
abbrev Scheme (Input Output M PK SK S : Type) :=
  SignatureAlg (RandomOracle.Computation Input Output) M PK SK S

/-- How attackers of type `A` are run: given the signing oracle and the public key,
with randomness and hashing from the ambient shared oracle, produce the candidate
forgery, the messages submitted for signing and whether the model's protocol was
respected — or `none` when there is no checkable forgery. -/
class Attacker (A : Type) (Input Output M PK S : Type) where
  run : A → (M → RandomOracle.Computation Input Output S) → PK →
    RandomOracle.Computation Input Output (Option ((M × S) × List M × Bool))

/-- Generate a key pair, run the attacker against the signing oracle, verify its
forgery, and require the forged message never to have been signed, admissible, and
the protocol respected. Everything shares one initially empty lazy random oracle. -/
noncomputable def game {A : Type} [Attacker A Input Output M PK S]
    (scheme : Scheme Input Output M PK SK S) (attacker : A)
    (admissible : M → List M → Prop := fun _ _ => True) [∀ message signed, Decidable (admissible message signed)] :
    ProbComp Bool :=
  RandomOracle.run do
    let (publicKey, secretKey) ← scheme.keygen
    match ← Attacker.run attacker (scheme.sign publicKey secretKey) publicKey with
    | none => return false
    | some ((message, signature), signed, wellFormed) =>
      let valid ← scheme.verify publicKey message signature
      return wellFormed && decide (message ∉ signed ∧ admissible message signed) && valid

/-! ### Ordinary attackers -/

/-- Given the public key, any computation with randomness, hashing and signing
access, ending in a candidate message/signature pair. -/
abbrev Adversary (scheme : Scheme Input Output M PK SK S) := SignatureAlg.UnforgeableAdversary scheme

/-- How an ordinary attacker's requests are answered. `random` and `hash` pass
through to the shared oracle unchanged; `sign m` runs the signer and records the
pair `(m, σ)` it returned. -/
abbrev oracle (sign : M → RandomOracle.Computation Input Output S) :
    QueryImpl (RandomOracle.Spec Input Output + (M →ₒ S))
      (WriterT (QueryLog (M →ₒ S)) (RandomOracle.Computation Input Output)) :=
  (RandomOracle.Spec Input Output).passthrough + QueryImpl.withLogging sign

noncomputable instance (scheme : Scheme Input Output M PK SK S) : Attacker (Adversary scheme) Input Output M PK S where
  run adversary sign publicKey := do
    let ((message, signature), log) ← (simulateQ (oracle sign) (adversary.main publicKey)).run
    return some ((message, signature), log.map Sigma.fst, true)

theorem not_wasQueried (log : QueryLog (M →ₒ S)) (message : M) :
    (!log.wasQueried message) = decide (message ∉ log.map Sigma.fst) := by
  show (!decide (log.getQ (· = message) ≠ [])) = _
  rw [← decide_not, decide_eq_decide]
  exact not_congr (QueryLog.getQ_ne_nil_iff_mem_map_fst log message)

/-- For ordinary attackers the experiment is VCVio's, in the random-oracle model. -/
theorem game_eq_unforgeableExperiment {scheme : Scheme Input Output M PK SK S} (adversary : Adversary scheme) :
    game scheme adversary = RandomOracle.run (SignatureAlg.unforgeableExperiment adversary) := by
  simp only [game, SignatureAlg.unforgeableExperiment, SignatureAlg.runWithSigningOracle_def,
    SignatureAlg.signingOracle, Attacker.run, oracle, bind_assoc, pure_bind, not_wasQueried, Bool.true_and, and_true]
  congr!

end Model.EufCma
