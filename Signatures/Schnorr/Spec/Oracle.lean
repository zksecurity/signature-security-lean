import Signatures.Model.RandomOracle
import Signatures.Model.EufCma
import Signatures.Schnorr.Spec.AGM
import Signatures.Schnorr.Spec.NonzeroNonce

/-! Readable Schnorr oracle interfaces for the ordinary and algebraic games.
Both nonce conventions use the same ordinary interface; the supplied signature
scheme chooses how to sample signing nonces. All hash queries share one random oracle.
-/

open OracleComp OracleSpec

namespace Schnorr.ROM

abbrev Request (M G : Type) := (advSpec Unit G M).Domain

namespace Request

@[match_pattern] abbrev random {M G : Type} (n : Nat) : Request M G := .inl (.inl n)
@[match_pattern] abbrev hash {M G : Type} (message : M) (commitment : G) : Request M G :=
  .inl (.inr (message, commitment))
@[match_pattern] abbrev sign {M G : Type} (message : M) : Request M G := .inr message

end Request

abbrev SigningLog (M G F : Type) := QueryLog (M →ₒ G × F)
abbrev OracleM (M G F : Type) :=
  WriterT (SigningLog M G F) (Model.RandomOracle.Computation (M × G) F)

/-- The honest scheme answers signing requests and records every delivered signature. -/
def oracle {F G M : Type}
    (scheme : SignatureAlg (Model.RandomOracle.Computation (M × G) F) M G F (G × F))
    (publicKey : G) (secret : F) : QueryImpl (advSpec F G M) (OracleM M G F)
  | Request.random n => liftM (Model.RandomOracle.random (Input := M × G) (Output := F) n)
  | Request.hash message commitment =>
      liftM (Model.RandomOracle.hash (Output := F) (message, commitment))
  | Request.sign message => scheme.signingOracle publicKey secret message

structure Result (M G F : Type) where
  message : M
  commitment : G
  response : F
  signingLog : SigningLog M G F

/-- Run the attacker with hashing and honest signing, retaining the signing history. -/
def run {F G M : Type}
    (scheme : SignatureAlg (Model.RandomOracle.Computation (M × G) F) M G F (G × F))
    (publicKey : G) (secret : F) (adversary : OracleComp (advSpec F G M) (M × (G × F))) :
    Model.RandomOracle.Computation (M × G) F (Result M G F) := do
  let ((message, commitment, response), signingLog) ←
    (simulateQ (oracle scheme publicKey secret) adversary).run
  return { message, commitment, response, signingLog }

end Schnorr.ROM

namespace Schnorr.AGM

abbrev OracleM (F G M : Type) := StateT (State M) (Model.RandomOracle.Computation (M × G) F)

def State.empty {M : Type} : State M := {}

abbrev State.signedMessages {M : Type} (state : State M) : List M := state.signed

variable {F G M : Type} [Field F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] [DecidableEq M]

abbrev random (n : Nat) : OracleM F G M (Fin (n + 1)) :=
  liftM (Model.RandomOracle.random (Input := M × G) (Output := F) n)

abbrev hash (message : M) (commitment : G) : OracleM F G M F :=
  liftM (Model.RandomOracle.hash (Output := F) (message, commitment))

abbrev sampleNonce : OracleM F G M F :=
  liftM (Model.RandomOracle.sample (Input := M × G) (Output := F) F)

/-- Algebraic hash requests supply a commitment; signing replies supply a new commitment. -/
def oracle (generator : G) (secret : F) :
    QueryImpl (AlgebraicGroupModel.Interaction.plainSpec (Group G) (Request M) (Reply F M))
      (OracleM F G M) := fun ⟨request, groups⟩ =>
  match request with
  | .random n => do
      if groups () ≠ [] then reject
      let value ← random n
      return scalarReply value
  | .hash message => do
      match groups () with
      | [commitment] =>
          let challenge ← hash message commitment
          return scalarReply challenge
      | _ =>
          reject
          return scalarReply (0 : F)
  | .sign message => do
      if groups () ≠ [] then
        reject
        return scalarReply (0 : F)
      else
        let nonce ← sampleNonce
        let commitment := nonce • generator
        let challenge ← hash message commitment
        modify fun state => { state with signed := state.signedMessages ++ [message] }
        return signingReply commitment (nonce + challenge * secret)

/-- The algebraic oracle with an arbitrary signing oracle: a signing reply delivers the
commitment as a group input and the response as data. -/
def oracleWith (sign : M → Model.RandomOracle.Computation (M × G) F (G × F)) :
    QueryImpl (AlgebraicGroupModel.Interaction.plainSpec (Group G) (Request M) (Reply F M))
      (OracleM F G M) := fun ⟨request, groups⟩ =>
  match request with
  | .random n => do
      if groups () ≠ [] then reject
      let value ← random n
      return scalarReply value
  | .hash message => do
      match groups () with
      | [commitment] =>
          let challenge ← hash message commitment
          return scalarReply challenge
      | _ =>
          reject
          return scalarReply (0 : F)
  | .sign message => do
      if groups () ≠ [] then
        reject
        return scalarReply (0 : F)
      else
        let (commitment, response) ← liftM (sign message)
        modify fun state => { state with signed := state.signedMessages ++ [message] }
        return signingReply commitment response

section Scheme
variable [SampleableType G]

/-- Honest signing is the scheme's signer under the secret key. -/
theorem oracle_eq_oracleWith (generator : G) (secret : F) :
    oracle (M := M) generator secret =
      oracleWith ((signature F G generator M).sign (secret • generator) secret) := by
  funext ⟨request, groups⟩
  cases request with
  | random n => rfl
  | hash message => rfl
  | sign message =>
    by_cases malformed : groups () ≠ []
    · simp [oracle, oracleWith, malformed]
    · funext state
      simp [oracle, oracleWith, malformed, signature, FiatShamir, Schnorr.sigma, sampleNonce, hash,
        Model.RandomOracle.sample, Model.RandomOracle.hash, Model.RandomOracle.Request.hash,
        OracleComp.liftM_eq_liftM_liftM, monad_norm]

structure Result (F G M : Type) where
  message : M
  commitment : G
  response : F
  state : State M

/-- Run the attacker against the shared hash oracle and the given signing oracle, from the
generator and public key; accept a single explained commitment as the signature's group part. -/
def runWith (sign : M → Model.RandomOracle.Computation (M × G) F (G × F))
    (adversary : Adversary F G M) (generator publicKey : G) :
    Model.RandomOracle.Computation (M × G) F (Option (Result F G M)) := do
  let ((output, _basis), state) ←
    (adversary.run (oracleWith sign) (initial generator publicKey)).run State.empty
  match output.value.groups () with
  | [commitment] =>
      let (message, response) := output.value.data
      return some { message, commitment, response, state }
  | _ => return none

/-- Accept a single explained commitment as the candidate signature's group component. -/
def run (generator : G) (secret : F) (adversary : Adversary F G M) :
    Model.RandomOracle.Computation (M × G) F (Option (Result F G M)) :=
  runWith ((signature F G generator M).sign (secret • generator) secret) adversary generator (secret • generator)

theorem runWith_sign (generator : G) (secret : F) (adversary : Adversary F G M) :
    runWith ((signature F G generator M).sign (secret • generator) secret) adversary generator (secret • generator) =
      run generator secret adversary := rfl

/-- Algebraic Schnorr attackers as an attacker model for the shared EUF-CMA experiment:
the forgery is the explained commitment with the response, and a malformed request or
an output without exactly one commitment loses. -/
@[instance_reducible]
def attacker (generator : G) : Model.EufCma.Attacker (Adversary F G M) (M × G) F M G (G × F) where
  run adversary sign publicKey :=
    (fun result => result.map fun forgery =>
      ((forgery.message, (forgery.commitment, forgery.response)), forgery.state.signedMessages, !forgery.state.malformed)) <$>
      runWith sign adversary generator publicKey

end Scheme

end Schnorr.AGM
