import Signatures.Model.AlgebraicOracle

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

/-- Execute the shared certified attacker directly with the signature oracles. -/
def run
    (terms : Message → List (Index × F)) (secret : F)
    (adversary : Adversary F Index Message G₁ G₂) (generator : G₁) (publicKey : G₂) :
    RandomOracle.Computation Index G₁ (Result F Message G₁) := do
  let ((output, _received), state) ←
    (adversary.run (oracle RandomOracle.random RandomOracle.hash
      (AlgebraicOracle.sign terms secret)) (initialInput generator publicKey)).run {}
  return result output state

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

end Model.DirectAGM
