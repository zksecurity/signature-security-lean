import Proofs.Runtime.Caliper.BLSCaller
import Proofs.Runtime.Caliper.CallerPresentation

/-! Shared source presentation for callers using the random/hash/sign packet
interface. Complete point representation converts all possible source replies;
local termination then supplies the controller's decreasing invariant. -/
namespace Signatures.Runtime.CaliperBackend.BLSCallerHandler
open Caliper BoundedSource OracleComp OracleSpec BLSCallerPackets
variable {w : Nat} {M R C G A B : Type} (service : BLSReply.Layouts w M R C G)
    (randomBound : Nat) (pointValid : ∀ point, service.point.valid point)

def representReply : (q : Request service randomBound) →
    (Model.LazyAGM.advSpec M M G).Range (query service randomBound q) → Reply service randomBound
  | .inl n, answer => .inl ⟨n, answer⟩
  | .inr (.inl _), point | .inr (.inr _), point => .inr ⟨point, pointValid point⟩

theorem representReply_eq (q : Request service randomBound) (represented : Reply service randomBound)
    (original : (Model.LazyAGM.advSpec M M G).Range (query service randomBound q))
    (related : replyMatches service randomBound q represented original) :
    represented = representReply service randomBound pointValid q original := by
  rcases q with n | (message | message)
  · cases represented with
    | inl random =>
        have equal := Prod.mk.inj (Sum.inl.inj related)
        congr 1
        exact Sigma.ext (Fin.ext equal.1) (by cases Fin.ext equal.1; exact heq_of_eq (Fin.ext equal.2))
    | inr point => cases related
  · cases represented with
    | inl random => cases related
    | inr point => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj related))
  · cases represented with
    | inl random => cases related
    | inr point => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj related))

variable (advance : A × Reply service randomBound → B ⊕ (Request service randomBound × A))
def terminationDomain (fuel : Nat) (pending : Request service randomBound × A) : Prop :=
  CallerMachine.Terminates (query service randomBound) (representReply service randomBound pointValid) advance fuel (.inr pending)

theorem headValid_iff_terminates (fuel : Nat) (head : B ⊕ (Request service randomBound × A)) :
    BLSCaller.HeadValid service randomBound (terminationDomain service randomBound pointValid advance) fuel head ↔
      CallerMachine.Terminates (query service randomBound) (representReply service randomBound pointValid) advance fuel head := by
  cases head <;> cases fuel <;> rfl

theorem termination_advance (remaining : Nat) (q : Request service randomBound) (c : A)
    (terminates : terminationDomain service randomBound pointValid advance (remaining + 1) (q, c))
    (represented : Reply service randomBound)
    (original : (Model.LazyAGM.advSpec M M G).Range (query service randomBound q))
    (related : replyMatches service randomBound q represented original) :
    BLSCaller.HeadValid service randomBound (terminationDomain service randomBound pointValid advance)
      remaining (advance (c, represented)) := by
  rw [headValid_iff_terminates, representReply_eq service randomBound pointValid q represented original related]
  exact terminates original

end Signatures.Runtime.CaliperBackend.BLSCallerHandler
