import Proofs.Runtime.Caliper.SchnorrROMPassBounds
import Proofs.Runtime.Caliper.CallerPresentation

/-! Derive the ROM pass's source machine and program from the caller's local
transitions. The mathematical reply conversion is never an executed free step:
actual handler replies already have the related bytes. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Pass
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} (config : Signing.Enumerated.Configuration w M F G)

theorem reply_injective : Function.Injective (CallerHandler.replyValue config) := by
  intro lhs rhs equal
  rcases lhs with (lhs | lhs) | lhs <;> rcases rhs with (rhs | rhs) | rhs
  all_goals simp only [CallerHandler.replyValue, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl] at equal
  all_goals cases Subtype.ext equal; rfl

variable [Zero F]
/-- Totalize the presentation outside represented replies. Only the selected
packet on a related actual reply enters the execution correspondence. -/
noncomputable def representedReply (q : CallerPackets.Request config)
    (answer : (FiatShamir.cmaOracleSpec M G F F).Range (CallerHandler.query config q)) : CallerPackets.Reply config := by
  classical
  exact if existsPacket : ∃ represented, SchnorrROM.Caller.replyMatches config q represented answer
    then existsPacket.choose else .inl (.inr ⟨0, trivial⟩)

theorem representedReply_eq (q : CallerPackets.Request config) (represented : CallerPackets.Reply config)
    (answer : (FiatShamir.cmaOracleSpec M G F F).Range (CallerHandler.query config q))
    (related : SchnorrROM.Caller.replyMatches config q represented answer) : represented = representedReply config q answer := by
  classical
  have existsPacket : ∃ represented, SchnorrROM.Caller.replyMatches config q represented answer := ⟨represented, related⟩
  rw [representedReply, dite_eq_left existsPacket]
  exact reply_injective config (related.trans existsPacket.choose_spec.symm)

variable (caller : Caller config A)
def Caller.Terminates (fuel : Nat) : Prop := ∀ input,
  CallerMachine.Terminates (CallerHandler.query config) (representedReply config) caller.advance fuel (caller.initial input)

variable (fuel : Nat) (terminates : caller.Terminates config fuel)
noncomputable def Caller.Source.ofCaller : Caller.Source config caller fuel where
  Input := config.point.Value
  machine := CallerMachine.ofCaller (CallerHandler.query config) (representedReply config) caller.advance caller.initial
  inputView := id
  stateView := Sum.inr
  program := CallerMachine.sourceOfCaller (CallerHandler.query config) (representedReply config) caller.advance caller.initial fuel terminates
  implements := CallerMachine.ofCaller_implements _ _ _ _ _ terminates
  advance := fun q current next view represented answer related =>
    CallerMachine.ofCaller_advance _ _ _ _ q current next view represented answer (representedReply_eq config q represented answer related)
  initial := fun input => CallerMachine.ofCaller_matches _ _ _ _ (caller.initial input)

theorem Caller.Source.ofCaller_run (input : config.point.Value) :
    (Caller.Source.ofCaller config caller fuel terminates).machine.unroll fuel (caller.initial input) =
      some <$> (Caller.Source.ofCaller config caller fuel terminates).program input :=
  (Caller.Source.ofCaller config caller fuel terminates).implements input

end Signatures.Runtime.CaliperBackend.SchnorrROM.Pass
