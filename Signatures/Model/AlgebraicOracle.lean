import Proofs.Model.LazyAGM
import Signatures.Model.RandomOracle

/-! The algebraic oracle shared by BLS, OOPS, and Proximity.

The state records only replies delivered to the attacker. Signing and verification
may query the shared random oracle internally without adding those points to the
attacker's algebraic basis. Repeated replies retain their chronological occurrences.
The exact connection to the certified AGM interaction is proved separately.
-/

open OracleComp OracleSpec

namespace Model.AlgebraicOracle

abbrev Request (Index Message : Type) := (LazyAGM.advSpec Index Message Unit).Domain

namespace Request

@[match_pattern] abbrev random {Index Message : Type} (n : Nat) : Request Index Message :=
  .inl (.inl n)
@[match_pattern] abbrev hash {Index Message : Type} (index : Index) : Request Index Message :=
  .inl (.inr index)
@[match_pattern] abbrev sign {Index Message : Type} (message : Message) : Request Index Message :=
  .inr message

end Request

structure State (Index Message Group : Type) where
  hashReplies : List (Index × Group) := []
  signingReplies : List (Message × Group) := []

def State.empty {Index Message Group : Type} : State Index Message Group := {}

def State.signedMessages {Index Message Group : Type} (state : State Index Message Group) :
    List Message := state.signingReplies.map fun (message, _) => message

abbrev OracleM (Index Message Group : Type) (N : Type → Type) :=
  StateT (State Index Message Group) N

/-- Forward randomness, and record each hash or signing reply actually returned to the attacker. -/
def oracle {Index Message Group : Type} {N : Type → Type} [Monad N]
    (random : QueryImpl unifSpec N) (hash : Index → N Group) (sign : Message → N Group) :
    QueryImpl (LazyAGM.advSpec Index Message Group) (OracleM Index Message Group N)
  | Request.random n => liftM (random n)
  | Request.hash index => do
      let point ← hash index
      modify fun state => { state with hashReplies := state.hashReplies ++ [(index, point)] }
      return point
  | Request.sign message => do
      let signature ← sign message
      modify fun state =>
        { state with signingReplies := state.signingReplies ++ [(message, signature)] }
      return signature

/-- The candidate signature and the signing history needed by the security game. -/
structure Result (Scalar Message Group : Type) where
  message : Message
  signature : Group
  signedMessages : List Message
  signingCoefficients : List Scalar

variable {F Index Message G₁ G₂ : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁]

/-- Hash the finite weighted list of bases specified by the signature scheme. -/
def hashMessage (terms : Message → List (Index × F)) (message : Message) :
    RandomOracle.Computation Index G₁ G₁ := LazyAGM.evalTerms (terms message)

def sign (terms : Message → List (Index × F)) (secret : F) (message : Message) :
    RandomOracle.Computation Index G₁ G₁ := do
  let point ← hashMessage terms message
  return secret • point

/-- Run the algebraic attacker and evaluate its explanation using only received points. -/
def run (terms : Message → List (Index × F)) (secret : F)
    (adversary : LazyAGM.Adversary F Index Message G₁ G₂) (generator : G₁) (publicKey : G₂) :
    RandomOracle.Computation Index G₁ (Result F Message G₁) := do
  let (output, state) ←
    (simulateQ (oracle RandomOracle.random RandomOracle.hash (sign terms secret))
      (adversary.main publicKey)).run State.empty
  return {
    message := output.mstar
    signature := output.β • generator + LazyAGM.weightedReplies output.γ state.hashReplies +
      LazyAGM.weightedReplies output.ξ state.signingReplies
    signedMessages := state.signedMessages
    signingCoefficients := output.ξ }

end Model.AlgebraicOracle
