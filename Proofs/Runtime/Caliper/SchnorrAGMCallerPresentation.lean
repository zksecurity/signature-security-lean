import Proofs.Runtime.Caliper.SchnorrAGMFullSource
import Proofs.Runtime.Caliper.SchnorrAGMCallerReplyEncoding
import Proofs.Runtime.Caliper.CallerQueryBounds

/-! Derive the Schnorr caller's machine and finite source tree from its actual
local transitions. The representation map is mathematical; related executed
replies already contain exactly these bytes. No complete solver is supplied. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Full.Caller
open Caliper OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G A : Type}
    (layout : CallerExtraction.Layouts w M F G qH qS randomBound A)
    [Zero F]
    (zeroValid : layout.service.scheme.scalar.valid (0 : F)) (caller : Caller layout)

def Terminates (fuel : Nat) : Prop := ∀ input,
  CallerMachine.Terminates (CallerHandler.query layout.service)
    (CallerHandler.representReply layout.service zeroValid) caller.advance fuel (caller.initial input)

variable {fuel : Nat} (invariant : Invariant layout caller fuel)
    (terminates : Terminates layout zeroValid caller fuel)

/-- Only local transitions, their invariant and branchwise termination enter
the constructor; the oracle machine and source tree are derived. -/
noncomputable def Source.ofCaller : Source layout caller fuel invariant where
  Input := layout.service.scheme.config.Value
  machine := CallerMachine.ofCaller (CallerHandler.query layout.service)
    (CallerHandler.representReply layout.service zeroValid) caller.advance caller.initial
  inputView := id
  stateView := Sum.inr
  program := CallerMachine.sourceOfCaller (CallerHandler.query layout.service)
    (CallerHandler.representReply layout.service zeroValid) caller.advance caller.initial fuel terminates
  implements := CallerMachine.ofCaller_implements _ _ _ _ _ terminates
  advance := fun _ _ _ q c _ next view represented original related =>
    CallerMachine.ofCaller_advance _ _ _ _ q c next view represented original
      (CallerHandler.representReply_eq layout.service zeroValid q represented original related)
  initial := fun input => CallerMachine.ofCaller_matches _ _ _ _ (caller.initial input)

theorem Source.ofCaller_run (input : layout.service.scheme.config.Value) :
    (Source.ofCaller layout zeroValid caller invariant terminates).machine.unroll fuel (caller.initial input) =
      some <$> (Source.ofCaller layout zeroValid caller invariant terminates).program input :=
  (Source.ofCaller layout zeroValid caller invariant terminates).implements input

variable (predicate : Interface.SourceRequest F G M → Prop) [DecidablePred predicate] (count : Nat)
def QueryBound (fuel : Nat) : Prop := ∀ input,
  CallerMachine.QueryBound (CallerHandler.query layout.service)
    (CallerHandler.representReply layout.service zeroValid) caller.advance predicate fuel count (caller.initial input)

omit invariant terminates in
theorem QueryBound.toTerminates (bounded : QueryBound layout zeroValid caller predicate count fuel) :
    Terminates layout zeroValid caller fuel :=
  fun input => CallerMachine.QueryBound.terminates _ _ _ _ (bounded input)

theorem Source.ofCaller_queryBound
    (bounded : QueryBound layout zeroValid caller predicate count fuel) (input : layout.service.scheme.config.Value) :
    IsQueryBoundP ((Source.ofCaller layout zeroValid caller invariant terminates).program input) predicate count :=
  CallerMachine.sourceOfCaller_queryBound _ _ _ predicate caller.initial fuel terminates count bounded input

def quotaDomain (remaining hashes signatures : Nat) (pending : layout.Request × A) : Prop :=
  CallerMachine.QueryBound (CallerHandler.query layout.service)
    (CallerHandler.representReply layout.service zeroValid) caller.advance
    (fun q => _root_.Schnorr.AGM.Reduction.hashRequest q = true) remaining hashes (.inr pending) ∧
  CallerMachine.QueryBound (CallerHandler.query layout.service)
    (CallerHandler.representReply layout.service zeroValid) caller.advance
    (fun q => _root_.Schnorr.AGM.Reduction.signRequest q = true) remaining signatures (.inr pending)

theorem headValid_iff_queryBounds (remaining hashes signatures : Nat)
    (head : layout.forgery.Value ⊕ (layout.Request × A)) :
    SchnorrAGM.Caller.HeadValid layout.service (quotaDomain layout zeroValid caller) remaining hashes signatures head ↔
      CallerMachine.QueryBound (CallerHandler.query layout.service)
        (CallerHandler.representReply layout.service zeroValid) caller.advance
        (fun q => _root_.Schnorr.AGM.Reduction.hashRequest q = true) remaining hashes head ∧
      CallerMachine.QueryBound (CallerHandler.query layout.service)
        (CallerHandler.representReply layout.service zeroValid) caller.advance
        (fun q => _root_.Schnorr.AGM.Reduction.signRequest q = true) remaining signatures head := by
  cases head <;> simp only [SchnorrAGM.Caller.HeadValid, quotaDomain, CallerMachine.QueryBound, and_self]

/-- Local hash/sign bounds provide the reduction's capacity reservation invariant. -/
def Invariant.ofQueryBounds
    (hashes : QueryBound layout zeroValid caller (fun q => _root_.Schnorr.AGM.Reduction.hashRequest q = true) qH fuel)
    (signatures : QueryBound layout zeroValid caller (fun q => _root_.Schnorr.AGM.Reduction.signRequest q = true) qS fuel) :
    Invariant layout caller fuel where
  domain := quotaDomain layout zeroValid caller
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
    rw [CallerHandler.representReply_eq layout.service zeroValid q represented original related,
      headValid_iff_queryBounds]
    have hashNext := valid.1.2 original
    have signNext := valid.2.2 original
    have hashCount : (if _root_.Schnorr.AGM.Reduction.hashRequest (CallerHandler.query layout.service q) = true
        then hashes - 1 else hashes) = hashes - CallerHandler.hashCharge layout.service q := by
      rcases q with args | (args | args) <;> simp [CallerHandler.hashCharge, CallerHandler.query,
        CallerHandler.nativeRequest, Interface.decodeRequest, Interface.request, _root_.Schnorr.AGM.Reduction.hashRequest]
    have signCount : (if _root_.Schnorr.AGM.Reduction.signRequest (CallerHandler.query layout.service q) = true
        then signatures - 1 else signatures) = signatures - CallerHandler.signCharge layout.service q := by
      rcases q with args | (args | args) <;> simp [CallerHandler.signCharge, CallerHandler.query,
        CallerHandler.nativeRequest, Interface.decodeRequest, Interface.request, _root_.Schnorr.AGM.Reduction.signRequest]
    exact ⟨hashCount ▸ hashNext, signCount ▸ signNext⟩
  initial := fun input => (headValid_iff_queryBounds layout zeroValid caller fuel qH qS (caller.initial input)).mpr
    ⟨hashes input, signatures input⟩

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Full.Caller
