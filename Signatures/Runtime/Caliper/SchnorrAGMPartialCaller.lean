import Signatures.Runtime.Caliper.SchnorrAGMFullSource
import Signatures.Runtime.Caliper.SchnorrAGMPartialReplies
import Signatures.Runtime.Caliper.PartialCaller

/-! Construct Schnorr source correspondence with immediate source-only returns
on unrepresented replies. Actual handler replies always decode to their exact
packet, so the existing Caliper program and resource bounds apply unchanged. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Full.Caller.Partial
open Caliper OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G A : Type}
    (layout : CallerExtraction.Layouts w M F G qH qS randomBound A) (caller : Caller layout)

def Terminates (fuel : Nat) : Prop := ∀ input,
  PartialCaller.Terminates (CallerHandler.query layout.service)
    (CallerHandler.decodeReply layout.service) caller.advance fuel (caller.initial input)

section Queries
variable (predicate : Interface.SourceRequest F G M → Prop) [DecidablePred predicate] (count : Nat)
def QueryBound (fuel : Nat) : Prop := ∀ input,
  PartialCaller.QueryBound (CallerHandler.query layout.service)
    (CallerHandler.decodeReply layout.service) caller.advance predicate fuel count (caller.initial input)

theorem QueryBound.terminates {fuel : Nat} (bounded : QueryBound layout caller predicate count fuel) :
    Terminates layout caller fuel :=
  fun input => PartialCaller.QueryBound.terminates _ _ _ _ (bounded input)
end Queries

def quotaDomain (remaining hashes signatures : Nat) (pending : layout.Request × A) : Prop :=
  PartialCaller.QueryBound (CallerHandler.query layout.service)
    (CallerHandler.decodeReply layout.service) caller.advance
    (fun q => _root_.Schnorr.AGM.Reduction.hashRequest q = true) remaining hashes (.inr pending) ∧
  PartialCaller.QueryBound (CallerHandler.query layout.service)
    (CallerHandler.decodeReply layout.service) caller.advance
    (fun q => _root_.Schnorr.AGM.Reduction.signRequest q = true) remaining signatures (.inr pending)

theorem headValid_iff_queryBounds (remaining hashes signatures : Nat)
    (head : layout.forgery.Value ⊕ (layout.Request × A)) :
    SchnorrAGM.Caller.HeadValid layout.service (quotaDomain layout caller) remaining hashes signatures head ↔
      PartialCaller.QueryBound (CallerHandler.query layout.service)
        (CallerHandler.decodeReply layout.service) caller.advance
        (fun q => _root_.Schnorr.AGM.Reduction.hashRequest q = true) remaining hashes head ∧
      PartialCaller.QueryBound (CallerHandler.query layout.service)
        (CallerHandler.decodeReply layout.service) caller.advance
        (fun q => _root_.Schnorr.AGM.Reduction.signRequest q = true) remaining signatures head := by
  cases head <;> simp only [SchnorrAGM.Caller.HeadValid, quotaDomain, PartialCaller.QueryBound, and_self]

def invariant {fuel : Nat}
    (hashes : QueryBound layout caller (fun q => _root_.Schnorr.AGM.Reduction.hashRequest q = true) qH fuel)
    (signatures : QueryBound layout caller (fun q => _root_.Schnorr.AGM.Reduction.signRequest q = true) qS fuel) :
    Invariant layout caller fuel where
  domain := quotaDomain layout caller
  allowed := by
    intro remaining hashes signatures q c valid
    have hashRoom := valid.1.1
    have signRoom := valid.2.1
    rcases q with args | (args | args)
    · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
    · exact ⟨Nat.succ_le_of_lt (hashRoom.resolve_left (fun h => h rfl)), Nat.zero_le _⟩
    · exact ⟨Nat.zero_le _, Nat.succ_le_of_lt (signRoom.resolve_left (fun h => h rfl))⟩
  advance := by
    intro remaining hashes signatures q c valid represented original related
    rw [headValid_iff_queryBounds]
    have decoded := (CallerHandler.decodeReply_eq_some layout.service q original represented).mpr related
    have hashNext := valid.1.2 original represented decoded
    have signNext := valid.2.2 original represented decoded
    have hashCount : (if _root_.Schnorr.AGM.Reduction.hashRequest (CallerHandler.query layout.service q) = true
        then hashes - 1 else hashes) = hashes - CallerHandler.hashCharge layout.service q := by
      rcases q with args | (args | args) <;> simp [CallerHandler.hashCharge, CallerHandler.query,
        CallerHandler.nativeRequest, Interface.decodeRequest, Interface.request, _root_.Schnorr.AGM.Reduction.hashRequest]
    have signCount : (if _root_.Schnorr.AGM.Reduction.signRequest (CallerHandler.query layout.service q) = true
        then signatures - 1 else signatures) = signatures - CallerHandler.signCharge layout.service q := by
      rcases q with args | (args | args) <;> simp [CallerHandler.signCharge, CallerHandler.query,
        CallerHandler.nativeRequest, Interface.decodeRequest, Interface.request, _root_.Schnorr.AGM.Reduction.signRequest]
    exact ⟨hashCount ▸ hashNext, signCount ▸ signNext⟩
  initial := fun input => (headValid_iff_queryBounds layout caller fuel qH qS (caller.initial input)).mpr
    ⟨hashes input, signatures input⟩

variable (fallback : layout.forgery.Value) {fuel : Nat}
    (reserved : Invariant layout caller fuel) (terminates : Terminates layout caller fuel)

noncomputable def correspondence : Source layout caller fuel reserved where
  Input := layout.service.scheme.config.Value
  machine := PartialCaller.machine (CallerHandler.query layout.service)
    (CallerHandler.decodeReply layout.service) caller.advance fallback caller.initial
  inputView := id
  stateView := Sum.inr
  program := fun input => PartialCaller.source (CallerHandler.query layout.service)
    (CallerHandler.decodeReply layout.service) caller.advance fallback fuel (caller.initial input)
  implements := PartialCaller.implements _ _ _ _ _ _ terminates
  advance := fun _ _ _ q c _ next view represented original related =>
    PartialCaller.advance_matches _ _ _ _ _ q c next view represented original
      ((CallerHandler.decodeReply_eq_some layout.service q original represented).mpr related)
  initial := fun input => PartialCaller.head_matches _ _ _ _ _ (caller.initial input)

omit fallback reserved in
include terminates in
theorem forgery_nonempty [Zero F] (zeroValid : layout.service.scheme.scalar.valid (0 : F))
    (input : layout.service.scheme.config.Value) : Nonempty layout.forgery.Value :=
  PartialCaller.Terminates.nonempty_result _ _ _ (CallerHandler.decodeReply_available layout.service zeroValid)
    (terminates input)

variable (predicate : Interface.SourceRequest F G M → Prop) [DecidablePred predicate] (count : Nat)
theorem correspondence_queryBound (bounded : QueryBound layout caller predicate count fuel)
    (input : layout.service.scheme.config.Value) :
    IsQueryBoundP ((correspondence layout caller fallback reserved terminates).program input) predicate count :=
  PartialCaller.QueryBound.source _ _ _ _ _ (bounded input)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Full.Caller.Partial
