import Proofs.Runtime.GeneralCallerBudget
import Signatures.Model.LazyAGM

/-! General callers for weighted signatures use separate hash-index and signing-
message types. Only the randomness arity is bounded by the request interface;
local attacker computation and the two query domains remain unrestricted. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.WeightedAGM

abbrev GeneralRequest (ι M : Type) (randomBound : Nat) :=
  (Fin (randomBound + 1) ⊕ ι) ⊕ M

def generalSpec (ι M G₁ : Type) (randomBound : Nat) : OracleSpec (GeneralRequest ι M randomBound)
  | .inl (.inl n) => Fin (n.val + 1)
  | .inl (.inr _) => G₁
  | .inr _ => G₁

def generalKind {ι M : Type} {randomBound : Nat} : GeneralRequest ι M randomBound → Fin 3
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 2

def defaultReply {ι M G₁ : Type} [Zero G₁] {randomBound : Nat} :
    (i : GeneralRequest ι M randomBound) → (generalSpec ι M G₁ randomBound).Range i
  | .inl (.inl n) => (0 : Fin (n.val + 1))
  | .inl (.inr _) => (0 : G₁)
  | .inr _ => (0 : G₁)

def generalReplies (ι M G₁ : Type) [Zero G₁] (randomBound : Nat) :
    GeneralCaller.ReplyContract (generalSpec ι M G₁ randomBound) where
  allows _ _ := True
  responds i := ⟨defaultReply i, trivial⟩

/-- Preserve both query domains and translate only the bounded randomness tag. -/
def generalSource {ι M G₁ : Type} (randomBound : Nat) :
    QueryImpl (generalSpec ι M G₁ randomBound) (OracleComp (Model.LazyAGM.advSpec ι M G₁))
  | .inl (.inl n) => liftM ((Model.LazyAGM.advSpec ι M G₁).query (.inl (.inl n.val)))
  | .inl (.inr i) => liftM ((Model.LazyAGM.advSpec ι M G₁).query (.inl (.inr i)))
  | .inr m => liftM ((Model.LazyAGM.advSpec ι M G₁).query (.inr m))

end Signatures.Runtime.WeightedAGM
