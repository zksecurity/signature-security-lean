import Signatures.Model.AlgebraicOracle
import Signatures.Model.EufCma

/-! Signature protocols for the shared interactive AGM adversary.

The attacker supplies actual group outputs and the shared library's algebraicity
certificate. Its explanation vectors use the chronological received basis. The
grouped coefficient interface is only an internal view for existing reductions.
-/

open OracleComp OracleSpec

namespace Model.DirectAGM

open AlgebraicGroupModel.Interaction
open LazyAGM.Interactive

variable {F Index Message G₁ G₂ : Type}
  [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

/-- The shared AGM adversary itself, specialized only to the signature protocol. -/
abbrev Adversary (F Index Message G₁ G₂ : Type)
    [Zero F] [AddCommMonoid G₁] [SMul F G₁] [AddMonoid G₂] [SMul F G₂] :=
  AlgebraicGroupModel.Interaction.Adversary F (Group G₁ G₂) Unit
    (Query Index Message) (Reply (ι := Index) (M := Message)) Message

/-- Positions of hash and signing replies in the shared library's received basis. -/
structure Positions where
  next : Nat := 1
  hashes : List Nat := []
  signatures : List Nat := []
  wellFormed : Bool := true

def Positions.hash (positions : Positions) : Positions :=
  { positions with next := positions.next + 1, hashes := positions.hashes ++ [positions.next] }

def Positions.sign (positions : Positions) : Positions :=
  { positions with
    next := positions.next + 1
    signatures := positions.signatures ++ [positions.next] }

def Positions.request (positions : Positions)
    (request : AlgebraicGroupModel.Interaction.Message (Query Index Message) (Group G₁ G₂)) :
    Positions :=
  { positions with wellFormed := positions.wellFormed &&
      (request.groups .signature).isEmpty && (request.groups .verification).isEmpty }

structure State (Message : Type) where
  positions : Positions := {}
  signedMessages : List Message := []

/-- Hash and signing requests have ordinary arguments; their replies supply group inputs. -/
def oracle {N : Type → Type} [Monad N]
    (random : QueryImpl unifSpec N) (hash : Index → N G₁) (sign : Message → N G₁) :
    QueryImpl (plainSpec (Group G₁ G₂) (Query Index Message) Reply)
      (StateT (State Message) N) := by
  intro ⟨request, groups⟩
  rcases request with ((n | index) | message)
  · exact do
      modify fun state => { state with positions := state.positions.request (Index := Index) (Message := Message) ⟨.inl (.inl n), groups⟩ }
      return ⟨← liftM (random n), fun _ => []⟩
  · exact do
      let point ← liftM (hash index)
      modify fun state => { state with
        positions := (state.positions.request (Index := Index) (Message := Message) ⟨.inl (.inr index), groups⟩).hash }
      return ⟨(), groupLists [point] []⟩
  · exact do
      let signature ← liftM (sign message)
      modify fun state => { state with
        positions := (state.positions.request (Index := Index) (Message := Message) ⟨.inr message, groups⟩).sign
        signedMessages := state.signedMessages ++ [message] }
      return ⟨(), groupLists [signature] []⟩

/-- The first outgoing signature's explanation. Missing outputs use an empty proof-side vector. -/
def coefficients (output : Explained F Message (Group G₁ G₂)) : List F :=
  (output.coefficients .signature).headD []

/-- Regroup an explanation for extraction; callers never supply this format. -/
def grouped (output : Explained F Message (Group G₁ G₂)) (positions : Positions) :
    LazyAGM.Output F Message where
  mstar := output.value.data
  β := LazyAGM.tokenCoeff (coefficients output) 0
  γ := positions.hashes.map (LazyAGM.tokenCoeff (coefficients output))
  ξ := positions.signatures.map (LazyAGM.tokenCoeff (coefficients output))

structure Result (F Message G₁ : Type) extends AlgebraicOracle.Result F Message G₁ where
  wellFormed : Bool

def result (output : Explained F Message (Group G₁ G₂)) (state : State Message) :
    Result F Message G₁ where
  message := output.value.data
  signature := (output.value.groups .signature).headD 0
  signedMessages := state.signedMessages
  signingCoefficients := (grouped output state.positions).ξ
  wellFormed := state.positions.wellFormed &&
    ((output.value.groups .signature).length == 1) &&
    (output.value.groups .verification).isEmpty

/-- Execute the shared certified attacker with the shared hash oracle and the given
signing oracle, starting from the generator and public key as its received inputs. -/
def runWith (sign : Message → RandomOracle.Computation Index G₁ G₁)
    (adversary : Adversary F Index Message G₁ G₂) (generator : G₁) (publicKey : G₂) :
    RandomOracle.Computation Index G₁ (Result F Message G₁) := do
  let ((output, _received), state) ←
    (adversary.run (oracle RandomOracle.random RandomOracle.hash sign) (initialInput generator publicKey)).run {}
  return result output state

/-- Execute the shared certified attacker directly with the signature oracles. -/
def run
    (terms : Message → List (Index × F)) (secret : F)
    (adversary : Adversary F Index Message G₁ G₂) (generator : G₁) (publicKey : G₂) :
    RandomOracle.Computation Index G₁ (Result F Message G₁) :=
  runWith (AlgebraicOracle.sign terms secret) adversary generator publicKey

/-- Algebraic attackers of the pairing family as an attacker model for the shared
EUF-CMA experiment: the explanation-checking interaction from the generator, with
`wellFormed` as the protocol flag. -/
@[instance_reducible]
def attacker (generator : G₁) : EufCma.Attacker (Adversary F Index Message G₁ G₂) Index G₁ Message G₂ G₁ where
  run adversary sign publicKey :=
    (fun forgery => some ((forgery.message, forgery.signature), forgery.signedMessages, forgery.wellFormed)) <$>
      runWith sign adversary generator publicKey

/-- The pairing-family scheme whose hash of a message is the combination of shared
oracle values prescribed by `terms`: secret `x`, public key `x • keyGenerator`,
signature `x • H(m)`, and verification `e(σ, keyGenerator) = e(H(m), pk)`. -/
noncomputable def scheme {Gₜ : Type} [AddCommGroup Gₜ] [Module F Gₜ] [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]
    [SampleableType F] [DecidableEq Gₜ] (terms : Message → List (Index × F)) (keyGenerator : G₂) :
    EufCma.Scheme Index G₁ Message G₂ F G₁ where
  keygen := do
    let secret ← RandomOracle.sample F
    return (secret • keyGenerator, secret)
  sign _ secret message := AlgebraicOracle.sign terms secret message
  verify publicKey message signature := do
    let hash ← AlgebraicOracle.hashMessage terms message
    return decide (BilinearGroup.pairing (F := F) (Gₜ := Gₜ) signature keyGenerator =
      BilinearGroup.pairing (F := F) (Gₜ := Gₜ) hash publicKey)

/-- Native EUF-CMA experiment; malformed protocol messages cannot win. -/
noncomputable def game {Gₜ : Type} [AddCommGroup Gₜ] [Module F Gₜ]
    [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]
    [SampleableType F] [SampleableType G₁] [DecidableEq Index]
    (terms : Message → List (Index × F)) (admissible : Message → List Message → Prop)
    (generator : G₁) (keyGenerator : G₂) (attack : Adversary F Index Message G₁ G₂) :
    ProbComp Bool := by
  classical
  exact RandomOracle.run do
    let secret ← RandomOracle.sample F
    let forgery ← run terms secret attack generator (secret • keyGenerator)
    let hash ← AlgebraicOracle.hashMessage terms forgery.message
    return decide (forgery.wellFormed ∧ admissible forgery.message forgery.signedMessages ∧
      BilinearGroup.pairing (F := F) (Gₜ := Gₜ) forgery.signature keyGenerator =
        BilinearGroup.pairing (F := F) (Gₜ := Gₜ) hash (secret • keyGenerator) ∧
      forgery.message ∉ forgery.signedMessages)

namespace ProofView

/-- Interpret the protocol in ordinary signature queries, retaining chronological positions. -/
def program
    (attack : OracleComp (explainedSpec F (Group G₁ G₂) (Query Index Message) Reply)
      (Explained F Message (Group G₁ G₂))) (positions : Positions) :
    OracleComp (LazyAGM.advSpec Index Message G₁) (LazyAGM.Output F Message) :=
  OracleComp.recOn
    (motive := fun _ => Positions → OracleComp (LazyAGM.advSpec Index Message G₁)
      (LazyAGM.Output F Message)) attack
    (fun output positions => pure (grouped output positions))
    (fun request _ next positions => by
      rcases request with ⟨⟨request, groups⟩, explanations⟩
      let positions := positions.request ⟨request, groups⟩
      rcases request with ((n | index) | message)
      · exact do
          let number ← (LazyAGM.advSpec Index Message G₁).query (.inl (.inl n))
          next ⟨number, fun _ => []⟩ positions
      · exact do
          let point ← (LazyAGM.advSpec Index Message G₁).query (.inl (.inr index))
          next ⟨(), groupLists [point] []⟩ positions.hash
      · exact do
          let signature ← (LazyAGM.advSpec Index Message G₁).query (.inr message)
          next ⟨(), groupLists [signature] []⟩ positions.sign) positions

/-- A total internal view of every shared-library attacker; no extra witness is requested. -/
def adversary (generator : G₁) (attack : Adversary F Index Message G₁ G₂) :
    LazyAGM.Adversary F Index Message G₁ G₂ where
  main publicKey := program (attack.main (initialInput generator publicKey)) {}

end ProofView


/-- The shared EUF-CMA experiment at the pairing-family scheme, for algebraic attackers,
is this native experiment. -/
theorem eufCma_game_eq {Gₜ : Type} [AddCommGroup Gₜ] [Module F Gₜ] [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]
    [SampleableType F] [SampleableType G₁] [DecidableEq Index] [DecidableEq Message] [DecidableEq Gₜ]
    (terms : Message → List (Index × F)) (admissible : Message → List Message → Prop)
    [∀ message signed, Decidable (admissible message signed)]
    (generator : G₁) (keyGenerator : G₂) (attack : Adversary F Index Message G₁ G₂) :
    letI := attacker (F := F) (Index := Index) (Message := Message) (G₂ := G₂) generator
    EufCma.game (scheme (G₁ := G₁) (Gₜ := Gₜ) terms keyGenerator) attack admissible =
      game (Gₜ := Gₜ) terms admissible generator keyGenerator attack := by
  let := attacker (F := F) (Index := Index) (Message := Message) (G₂ := G₂) generator
  simp only [EufCma.game, scheme, EufCma.Attacker.run, game, run, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_apply]
  congr! 7
  simp [Bool.decide_and, Bool.and_comm, Bool.and_left_comm]

/-! ### Several group elements per key and per signature -/

/-- `Positions.sign` for a reply that delivers `count` group elements. -/
def Positions.signMany (positions : Positions) (count : Nat) : Positions :=
  { positions with
    next := positions.next + count
    signatures := positions.signatures ++ (List.range count).map (positions.next + ·) }

/-- `oracle` for signers whose reply is a list of signature-group elements. -/
def oracleTuple {N : Type → Type} [Monad N]
    (random : QueryImpl unifSpec N) (hash : Index → N G₁) (sign : Message → N (List G₁)) :
    QueryImpl (plainSpec (Group G₁ G₂) (Query Index Message) Reply)
      (StateT (State Message) N) := by
  intro ⟨request, groups⟩
  rcases request with ((n | index) | message)
  · exact do
      modify fun state => { state with positions := state.positions.request (Index := Index) (Message := Message) ⟨.inl (.inl n), groups⟩ }
      return ⟨← liftM (random n), fun _ => []⟩
  · exact do
      let point ← liftM (hash index)
      modify fun state => { state with
        positions := (state.positions.request (Index := Index) (Message := Message) ⟨.inl (.inr index), groups⟩).hash }
      return ⟨(), groupLists [point] []⟩
  · exact do
      let points ← liftM (sign message)
      modify fun state => { state with
        positions := (state.positions.request (Index := Index) (Message := Message) ⟨.inr message, groups⟩).signMany points.length
        signedMessages := state.signedMessages ++ [message] }
      return ⟨(), groupLists points []⟩

structure TupleResult (Message G₁ : Type) where
  message : Message
  signature : List G₁
  signedMessages : List Message
  wellFormed : Bool

def tupleResult (output : Explained F Message (Group G₁ G₂)) (state : State Message) : TupleResult Message G₁ where
  message := output.value.data
  signature := output.value.groups .signature
  signedMessages := state.signedMessages
  wellFormed := state.positions.wellFormed && (output.value.groups .verification).isEmpty

/-- Execute the certified attacker from the generator and the public key's `𝔾₂` components,
with a signer that returns several `𝔾₁` elements per signature. -/
def runTuple (sign : Message → RandomOracle.Computation Index G₁ (List G₁))
    (adversary : Adversary F Index Message G₁ G₂) (generator : G₁) (keys : List G₂) :
    RandomOracle.Computation Index G₁ (TupleResult Message G₁) := do
  let ((output, _received), state) ←
    (adversary.run (oracleTuple RandomOracle.random RandomOracle.hash sign) ⟨(), groupLists [generator] keys⟩).run {}
  return tupleResult output state

/-- The algebraic attacker model for schemes whose keys and signatures are tuples of group
elements: the generator and the key's `𝔾₂` components are the received inputs, each signing
reply delivers the signature's `𝔾₁` components, and the forgery is decoded from the explained
`𝔾₁` outputs — a wrong shape is no forgery. -/
@[instance_reducible]
def attackerTuple {PK S : Type} (generator : G₁) (keys : PK → List G₂) (encode : S → List G₁)
    (decode : List G₁ → Option S) :
    EufCma.Attacker (Adversary F Index Message G₁ G₂) Index G₁ Message PK S where
  run adversary sign publicKey :=
    (fun forgery => (decode forgery.signature).map fun s =>
      ((forgery.message, s), forgery.signedMessages, forgery.wellFormed)) <$>
      runTuple (fun message => encode <$> sign message) adversary generator (keys publicKey)

end Model.DirectAGM
