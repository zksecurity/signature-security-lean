import Proofs.Runtime.Caliper.CallerControl

/-! Correctness of the complete generated caller controller, including initial
return, calls, early return after a call, and observable fuel cutoff. The domain
reservation is preserved on supported handler outputs, not assumed globally. -/

namespace Signatures.Runtime.CaliperBackend.CallerControl
open Caliper OracleComp OracleSpec

variable {w : Nat} {C Q R B S : Type} (layout : CallerStep.Layouts w C Q R B S)
    {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    (advance : C × R → B ⊕ (Q × C))
    (continuation : Realizer .unit (CallerStep.resume layout) (CallerStep.next layout) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)
    {handler : Interactive.Code w} {H : Q × S → OracleComp spec (R × S)}
    (invariant : Nat → Frame C Q S → Prop) (ready : Q × S → Prop)
    (handlerRefines : Interactive.RefinesOn ready port .unit (CallerStep.request layout) (CallerStep.reply layout) H handler)
    (available : ∀ remaining value, invariant (remaining + 1) value → ready (value.1.1, value.2))

include handlerRefines available in
theorem body_refines (remaining : Nat) :
    Interactive.RefinesOn (invariant (remaining + 1)) port .unit
      (CallerStep.frame layout) (iteration layout) (bodySource advance H)
      (body layout port advance continuation localNameFits handler) := by
  have step : Interactive.RefinesOn (invariant (remaining + 1)) port .unit
      (CallerStep.frame layout) (CallerStep.output layout) (CallerStep.denote advance H)
      (CallerStep.code layout port advance continuation localNameFits handler) :=
    fun tape value valid before holds =>
      CallerStep.refines layout port advance continuation localNameFits handlerRefines
        tape value (available remaining value valid) before holds
  have refined := step.seq ((Interactive.Refines.compute port .unit (route layout)).on (fun _ => True)) (by intros; trivial)
  unfold bodySource body
  simpa only [bind_pure_comp] using refined

variable (preserves : ∀ remaining value, invariant (remaining + 1) value →
  ∀ reply ∈ support (H (value.1.1, value.2)), Valid invariant remaining (advance (value.1.2, reply.1), reply.2))

include preserves in
theorem body_preserves (remaining : Nat) (value : Frame C Q S) (valid : invariant (remaining + 1) value)
    (output) (reached : output ∈ support (bodySource advance H value)) :
    Sum.elim (fun _ => True) (invariant remaining) output := by
  simp only [bodySource, CallerStep.denote, Functor.map_map, support_map, Set.mem_image] at reached
  obtain ⟨reply, supported, rfl⟩ := reached
  have valid := preserves remaining value valid reply supported
  cases h : advance (value.1.2, reply.1) with
  | inl value => simp [select]
  | inr pending => simpa [select, Valid, h] using valid

include handlerRefines available preserves in
theorem fromState_refines (fuel : Nat) :
    Interactive.RefinesOn (invariant fuel) port .unit (CallerStep.frame layout) (CallerStep.output layout)
      (denote advance H fuel) (fromState layout port advance continuation localNameFits handler fuel) :=
  Interactive.RefinesOn.loop (CallerStep.frame layout) (CallerStep.output layout) invariant
    (width_pos layout.width) (iteration layout).fits
    (body_refines layout port advance continuation localNameFits invariant ready handlerRefines available)
    ((Interactive.Refines.compute port .unit (stop layout)).on (invariant 0))
    (body_preserves advance invariant preserves) fuel

include handlerRefines available preserves in
theorem fromPacket_refines (fuel : Nat) :
    Interactive.RefinesOn (Valid invariant fuel) port .unit (CallerStep.output layout) (CallerStep.output layout)
      (start advance H fuel) (fromPacket layout port advance continuation localNameFits handler fuel) := by
  have dispatched := Interactive.RefinesOn.dispatch (result layout) (CallerStep.frame layout) (CallerStep.output layout)
    ((Interactive.Refines.compute port .unit (done layout)).on (fun _ => True))
    (fromState_refines layout port advance continuation localNameFits invariant ready handlerRefines available preserves fuel)
    (width_pos layout.width) (choice layout).fits
  have prepared := (Interactive.Refines.compute port .unit (distribute layout)).on (Valid invariant fuel)
  have combined := prepared.seq dispatched (by
    intro value valid output reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst output
    rcases value with ⟨value | pending, saved⟩ <;> exact valid)
  have equal : (fun value : Packet C Q B S => pure (SumContext.view value) >>=
      Sum.elim (fun value => (pure (returned value) : OracleComp spec _)) (denote advance H fuel)) =
      start advance H fuel := by
    funext value
    rcases value with ⟨value | pending, saved⟩ <;> simp [start, SumContext.view, returned]
  rw [equal] at combined
  exact combined

variable {A : Type} (input : Representation w A) (initial : A → B ⊕ (Q × C))
    (initialCode : Realizer .unit input (CallerStep.next layout) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + layout.store.encoding.words < 2 ^ w)

include handlerRefines available preserves in
theorem program_refines (fuel : Nat) (admissible : A × S → Prop)
    (initialValid : ∀ value, admissible value → Valid invariant fuel (initial value.1, value.2)) :
    Interactive.RefinesOn admissible port .unit (input.prod layout.store inputFits) (CallerStep.output layout)
      (fun value => start advance H fuel (initial value.1, value.2))
      (program layout port advance continuation localNameFits handler input initial initialCode initialNameFits inputFits fuel) := by
  have prepared := (Interactive.Refines.compute port .unit
    (initialCode.retain (by decide) layout.store layout.width initialNameFits inputFits (CallerStep.output layout).fits)).on admissible
  have combined := prepared.seq
    (fromPacket_refines layout port advance continuation localNameFits invariant ready handlerRefines available preserves fuel)
    (by
      intro value valid output reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst output
      exact initialValid value valid)
  unfold program
  simpa only [pure_bind] using combined

end Signatures.Runtime.CaliperBackend.CallerControl
