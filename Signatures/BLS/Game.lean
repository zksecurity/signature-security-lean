import Signatures.Model.PairingCurve
import Signatures.BLS.Spec.LazyAGM
import Signatures.BLS.Spec.ROM
import Signatures.Model.DirectAGM
import Signatures.Model.EufCma

/-! BLS security games, independent of any execution model or resource certificate.
`signature` is BLS as a scheme; `eufCma` and `agm` are one experiment, the shared
EUF-CMA game (`Model.EufCma.game`), for two attacker models: ordinary oracle
programs, and algebraic attackers that explain every group element they output as
a combination of the elements received so far (`g₁`, then each hash and signing
reply in order), a malformed interaction being flagged and losing. `eufCma_eq`
writes the ordinary experiment out: the attacker's `random`/`hash` requests pass to
one lazy random oracle `H : Message → 𝔾₁`, started empty and shared with the signer
and the verifier, and `sign m` returns `x • H(m)` and records `m`.
Security bounds are in `Statement.lean`; execution contracts remain separate. -/

open OracleComp OracleSpec
open Model

namespace BLS.Game

variable (curve : Model.PairingCurve) (securityParameter : Nat)
  {Message : Type} [DecidableEq Message]

local notation "𝔽" => curve.Scalar securityParameter
local notation "𝔾₁" => curve.SignatureGroup securityParameter
local notation "𝔾₂" => curve.KeyGroup securityParameter
local notation "𝔾ₜ" => curve.TargetGroup securityParameter
local notation "g₁" => curve.generator securityParameter
local notation "g₂" => curve.keyGenerator securityParameter

/-- Arbitrary internal computation with algebraic group outputs. -/
abbrev AlgebraicAdversary := Model.DirectAGM.Adversary (curve.Scalar securityParameter)
  Message Message (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)

/-- Arbitrary message/signature output, without algebraic explanations. -/
abbrev UnrestrictedAdversary := ROM.AdversaryPK Message
  (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)

/-- BLS itself: the secret key is `x`, the public key `x • g₂`, a signature `x • H(m)`,
and verification checks `e(σ, g₂) = e(H(m), pk)`. -/
noncomputable def signature : EufCma.Scheme Message 𝔾₁ Message 𝔾₂ 𝔽 𝔾₁ where
  keygen := do
    let secret ← RandomOracle.sample 𝔽
    return (secret • g₂, secret)
  sign _ secret message := do
    let hash ← RandomOracle.hash message
    return secret • hash
  verify publicKey message signature := do
    let hash ← RandomOracle.hash message
    return decide (BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) signature g₂ =
      BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) hash publicKey)

/-- BLS is the pairing-family scheme with one hash term per message. -/
theorem signature_eq_scheme :
    signature curve securityParameter (Message := Message) =
      DirectAGM.scheme (G₁ := 𝔾₁) (Gₜ := 𝔾ₜ) LazyAGM.terms g₂ := by
  unfold signature DirectAGM.scheme
  congr 1
  · funext _ secret message
    simp [Model.AlgebraicOracle.sign, Model.AlgebraicOracle.hashMessage, LazyAGM.terms, Model.LazyAGM.evalTerms,
      RandomOracle.hash]
  · funext publicKey message point
    simp [Model.AlgebraicOracle.hashMessage, LazyAGM.terms, Model.LazyAGM.evalTerms, RandomOracle.hash]

/-- Algebraic attackers, run through the explanation-checking interaction from `g₁`. -/
noncomputable instance : EufCma.Attacker (AlgebraicAdversary curve securityParameter (Message := Message))
    Message 𝔾₁ Message 𝔾₂ 𝔾₁ :=
  DirectAGM.attacker g₁

/-- Standard EUF-CMA for BLS: the shared experiment at `signature`, for an ordinary attacker. -/
noncomputable def eufCma
    (adversary : EufCma.Adversary (signature curve securityParameter (Message := Message))) : ProbComp Bool :=
  EufCma.game (signature curve securityParameter (Message := Message)) adversary

/-- The same experiment for an algebraic attacker. -/
noncomputable def agm
    (adversary : AlgebraicAdversary curve securityParameter (Message := Message)) : ProbComp Bool :=
  EufCma.game (signature curve securityParameter (Message := Message)) adversary

/-- How an ordinary attacker's requests are answered. `random n` draws a uniform element
of `Fin (n + 1)`; `hash m` returns `H(m)` from the shared lazy oracle; `sign m` returns
`x • H(m)` and records `m` as signed. -/
noncomputable def oracle (secret : 𝔽) :
    QueryImpl (ROM.advSpec Message 𝔾₁) (WriterT (QueryLog (Message →ₒ 𝔾₁)) (RandomOracle.Computation Message 𝔾₁))
  | ROM.Request.random n => liftM (RandomOracle.random (Input := Message) (Output := 𝔾₁) n)
  | ROM.Request.hash message => liftM (RandomOracle.hash (Output := 𝔾₁) message)
  | ROM.Request.sign message => do
      let signature := secret • (← liftM (RandomOracle.hash (Output := 𝔾₁) message))
      tell [⟨message, signature⟩]
      return signature

omit [DecidableEq Message] in
theorem oracle_eq (secret : 𝔽) :
    oracle curve securityParameter (Message := Message) secret =
      EufCma.oracle ((signature curve securityParameter).sign (secret • g₂) secret) := by
  funext request
  rcases request with (n | message) | message
  · simp [oracle, EufCma.oracle, ROM.Request.random, RandomOracle.random]
  · simp [oracle, EufCma.oracle, ROM.Request.hash, RandomOracle.hash]
  · show WriterT.run _ = WriterT.run _
    simp [signature, RandomOracle.hash, WriterT.run_tell]

/-- The ordinary experiment, written out: generate `pk = x • g₂`, run the attacker
against `oracle x`, hash the forged message through the same oracle, and accept a
valid signature on a message that was never signed. -/
theorem eufCma_eq (adversary : EufCma.Adversary (signature curve securityParameter (Message := Message))) :
    eufCma curve securityParameter adversary = RandomOracle.run do
      let secret ← RandomOracle.sample 𝔽
      let publicKey := secret • g₂
      let ((message, forged), signingLog) ←
        (simulateQ (oracle curve securityParameter secret) (adversary.main publicKey)).run
      let hash ← RandomOracle.hash message
      return !signingLog.wasQueried message &&
        decide (BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) forged g₂ = BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) hash publicKey) := by
  rw [eufCma, EufCma.game_eq_unforgeableExperiment]
  simp only [SignatureAlg.unforgeableExperiment, SignatureAlg.runWithSigningOracle_def, SignatureAlg.signingOracle,
    oracle_eq, EufCma.oracle, signature, bind_assoc, pure_bind]
  congr!

end BLS.Game
