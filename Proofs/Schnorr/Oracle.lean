import Signatures.Schnorr.Spec.Oracle

/-! The readable handlers preserve the original Schnorr oracle programs exactly. -/

open OracleComp OracleSpec

namespace Schnorr.ROM

theorem oracle_eq {F G M : Type}
    (scheme : SignatureAlg (Model.RandomOracle.Computation (M × G) F) M G F (G × F))
    (publicKey : G) (secret : F) :
    oracle scheme publicKey secret =
      (Model.RandomOracle.Spec (M × G) F).passthrough + scheme.signingOracle publicKey secret := by
  funext request
  rcases request with (n | ⟨message, commitment⟩) | message <;> rfl

theorem run_eq {F G M : Type}
    (scheme : SignatureAlg (Model.RandomOracle.Computation (M × G) F) M G F (G × F))
    (publicKey : G) (secret : F) (adversary : OracleComp (advSpec F G M) (M × (G × F))) :
    run scheme publicKey secret adversary =
      (fun ((message, commitment, response), signingLog) =>
        ({ message, commitment, response, signingLog } : Result M G F)) <$>
      scheme.runWithSigningOracle publicKey secret adversary := by
  simp only [run, oracle_eq, SignatureAlg.runWithSigningOracle, bind_pure_comp]

variable {F G M : Type} [Field F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] [DecidableEq M]

theorem verify_eq (generator publicKey : G) (message : M) (candidate : G × F) :
    (signature F G generator M).verify publicKey message candidate = (do
      let challenge ← Model.RandomOracle.hash (message, candidate.1)
      return decide (candidate.2 • generator = candidate.1 + challenge • publicKey)) := by
  rcases candidate with ⟨commitment, response⟩
  simp [signature, FiatShamir, Schnorr.sigma, Model.RandomOracle.hash,
    Model.RandomOracle.Request.hash, OracleComp.liftM_eq_liftM_liftM, monad_norm]

omit [DecidableEq M] in
theorem nonzero_verify_eq [SampleableType Fˣ]
    (generator publicKey : G) (message : M) (candidate : G × F) :
    (NonzeroNonce.signature (F := F) (M := M) generator).verify publicKey message candidate = (do
      let challenge ← Model.RandomOracle.hash (message, candidate.1)
      return decide (candidate.2 • generator = candidate.1 + challenge • publicKey)) := by
  rcases candidate with ⟨commitment, response⟩
  simp [NonzeroNonce.signature, NonzeroNonce.sigma, FiatShamir, Schnorr.sigma,
    Model.RandomOracle.hash, Model.RandomOracle.Request.hash,
    OracleComp.liftM_eq_liftM_liftM, monad_norm]

end Schnorr.ROM

namespace Schnorr.AGM

variable {F G M : Type} [Field F] [SampleableType F]
  [AddCommGroup G] [Module F G]

theorem oracle_eq_handler (generator : G) (secret : F) :
    oracle (M := M) generator secret = handler generator secret := by
  funext request
  rcases request with ⟨request, groups⟩
  cases request <;> rfl

end Schnorr.AGM
