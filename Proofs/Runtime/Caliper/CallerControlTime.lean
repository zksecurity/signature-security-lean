import Proofs.Runtime.Caliper.CallerControlRouting

/-! Time of the complete generated controller, including one initialization,
early return, cutoff, each handler call, and all saved-state and tag copying. -/

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
    {handlerTime localTime : Nat}
    (handlerBound : Interactive.TimeBoundOn ready port .unit (CallerStep.request layout) handler handlerTime)
    (localBound : ∀ value, continuation.time value ≤ localTime)

include handlerRefines available handlerBound localBound in
theorem body_time (remaining : Nat) :
    Interactive.TimeBoundOn (invariant (remaining + 1)) port .unit (CallerStep.frame layout)
      (body layout port advance continuation localNameFits handler)
      (handlerTime + localTime + 164 * CallerStep.width layout + 4) := by
  have stepRefines : Interactive.RefinesOn (invariant (remaining + 1)) port .unit
      (CallerStep.frame layout) (CallerStep.output layout) (CallerStep.denote advance H)
      (CallerStep.code layout port advance continuation localNameFits handler) :=
    fun tape value valid before holds =>
      CallerStep.refines layout port advance continuation localNameFits handlerRefines
        tape value (available remaining value valid) before holds
  have stepBound : Interactive.TimeBoundOn (invariant (remaining + 1)) port .unit
      (CallerStep.frame layout) (CallerStep.code layout port advance continuation localNameFits handler)
      (handlerTime + localTime + 80 * CallerStep.width layout) :=
    fun tape value valid before holds =>
      CallerStep.time layout port advance continuation localNameFits handlerRefines handlerBound localBound
        tape value (available remaining value valid) before holds
  have routed := (Interactive.TimeBound.compute (port := port) (cost := .unit) (route layout) _ (route_time layout)).on (fun _ => True)
  exact (Interactive.TimeBoundOn.seq stepRefines stepBound routed (by intros; trivial)).mono (by omega)

variable (preserves : ∀ remaining value, invariant (remaining + 1) value →
  ∀ reply ∈ support (H (value.1.1, value.2)), Valid invariant remaining (advance (value.1.2, reply.1), reply.2))

include handlerRefines available handlerBound localBound preserves in
theorem fromState_time (fuel : Nat) :
    Interactive.TimeBoundOn (invariant fuel) port .unit (CallerStep.frame layout)
      (fromState layout port advance continuation localNameFits handler fuel)
      (36 * CallerStep.width layout + fuel * (handlerTime + localTime + 172 * CallerStep.width layout + 6)) := by
  have bounded := Interactive.TimeBoundOn.loop (CallerStep.frame layout) (CallerStep.output layout) invariant
    (width_pos layout.width) (iteration layout).fits
    (body_refines layout port advance continuation localNameFits invariant ready handlerRefines available)
    (body_time layout port advance continuation localNameFits invariant ready handlerRefines available handlerBound localBound)
    ((Interactive.TimeBound.compute (port := port) (cost := .unit) (stop layout) _ (stop_time layout)).on (invariant 0))
    (body_preserves advance invariant preserves) fuel
  apply bounded.mono
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  rw [Interactive.loopOverhead_unit]
  have bounds := sizes layout
  omega

include handlerRefines available handlerBound localBound preserves in
theorem fromPacket_time (fuel : Nat) :
    Interactive.TimeBoundOn (Valid invariant fuel) port .unit (CallerStep.output layout)
      (fromPacket layout port advance continuation localNameFits handler fuel)
      (68 * CallerStep.width layout + 4 + fuel * (handlerTime + localTime + 172 * CallerStep.width layout + 6)) := by
  have dispatched := Interactive.TimeBoundOn.dispatch (result layout) (CallerStep.frame layout)
    ((Interactive.TimeBound.compute (port := port) (cost := .unit) (done layout) _ (done_time layout)).on (fun _ => True))
    (fromState_time layout port advance continuation localNameFits invariant ready handlerRefines available handlerBound localBound preserves fuel)
    (width_pos layout.width) (choice layout).fits
  have prepared := (Interactive.Refines.compute port .unit (distribute layout)).on (Valid invariant fuel)
  have combined := Interactive.TimeBoundOn.seq prepared
    ((Interactive.TimeBound.compute (port := port) (cost := .unit) (distribute layout) _ (distribute_time layout)).on (Valid invariant fuel))
    dispatched (by
      intro value valid output reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst output
      rcases value with ⟨value | pending, saved⟩ <;> exact valid)
  apply combined.mono
  rw [Interactive.dispatchTime_unit]
  have bounds := sizes layout
  omega

variable {A : Type} (input : Representation w A) (initial : A → B ⊕ (Q × C))
    (initialCode : Realizer .unit input (CallerStep.next layout) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + layout.store.encoding.words < 2 ^ w)

include handlerRefines available handlerBound localBound preserves in
theorem program_time (fuel : Nat) (admissible : A × S → Prop)
    (initialValid : ∀ value, admissible value → Valid invariant fuel (initial value.1, value.2))
    (initialTime : Nat) (initialBound : ∀ value, initialCode.time value ≤ initialTime) :
    Interactive.TimeBoundOn admissible port .unit (input.prod layout.store inputFits)
      (program layout port advance continuation localNameFits handler input initial initialCode initialNameFits inputFits fuel)
      (initialTime + 8 * input.encoding.words + 88 * CallerStep.width layout + 4 +
        fuel * (handlerTime + localTime + 172 * CallerStep.width layout + 6)) := by
  let init := initialCode.retain (by decide) layout.store layout.width initialNameFits inputFits (CallerStep.output layout).fits
  have prepared := (Interactive.Refines.compute port .unit init).on admissible
  have initialBound : ∀ value, init.time value ≤ initialTime + 8 * input.encoding.words + 20 * CallerStep.width layout := by
    intro value
    have copied := initialCode.retain_time_unit_le layout.store layout.width initialNameFits inputFits (CallerStep.output layout).fits value
    have initial := initialBound value.1
    have bounds := sizes layout
    exact copied.trans (by omega)
  have combined := Interactive.TimeBoundOn.seq prepared
    ((Interactive.TimeBound.compute (port := port) (cost := .unit) init _ initialBound).on admissible)
    (fromPacket_time layout port advance continuation localNameFits invariant ready handlerRefines available handlerBound localBound preserves fuel)
    (by
      intro value valid output reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst output
      exact initialValid value valid)
  exact combined.mono (by omega)

end Signatures.Runtime.CaliperBackend.CallerControl
