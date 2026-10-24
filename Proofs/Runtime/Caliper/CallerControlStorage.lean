import Proofs.Runtime.Caliper.CallerControlTime

/-! Stored instructions, generated names and word acceptance for the complete
caller controller. Bounded loops charge every stored copy of their body. -/

namespace Signatures.Runtime.CaliperBackend
open Caliper OracleComp OracleSpec
variable {w : Nat}

theorem Interactive.loop_names {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    {body stop : Interactive.Code w} {slots : Nat}
    (bodyNames : WordIO.NamesAccounted (body.lower port) slots)
    (stopNames : WordIO.NamesAccounted (stop.lower port) slots)
    (resultWords stateWords fuel : Nat) :
    WordIO.NamesAccounted ((Interactive.loop body stop resultWords stateWords fuel).lower port) slots := by
  induction fuel with
  | zero => exact stopNames
  | succ fuel ih => exact bodyNames.seq (Interactive.dispatch_names port (left := .compute .skip)
      (WordIO.NamesAccounted.compute (skip_names slots)) ih resultWords stateWords)

namespace CallerControl
variable {C Q R B S : Type} (layout : CallerStep.Layouts w C Q R B S)
    {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    (advance : C × R → B ⊕ (Q × C))
    (continuation : Realizer .unit (CallerStep.resume layout) (CallerStep.next layout) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w) (handler : Interactive.Code w)

def iterationWords : Nat := (handler.lower port).descriptionWords + descriptionWords continuation.code +
  742 * CallerStep.width layout + 389

theorem body_words : ((body layout port advance continuation localNameFits handler).lower port).descriptionWords ≤
    (handler.lower port).descriptionWords + descriptionWords continuation.code + 690 * CallerStep.width layout + 346 := by
  have step := CallerStep.words layout port advance continuation localNameFits handler
  have routed := route_words layout
  simp only [body, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega

theorem fromState_words (fuel : Nat) :
    ((fromState layout port advance continuation localNameFits handler fuel).lower port).descriptionWords ≤
      117 * CallerStep.width layout + 54 + fuel * iterationWords layout port advance continuation handler := by
  have bodyBound := body_words layout port advance continuation localNameFits handler
  have stopBound := stop_words layout
  have bounds := sizes layout
  rw [fromState, Interactive.loop_descriptionWords]
  simp only [Interactive.Code.lower, WordIO.Code.descriptionWords_compute]
  apply Nat.add_le_add (by omega)
  apply Nat.mul_le_mul_left
  dsimp only [iterationWords]
  omega

theorem fromPacket_words (fuel : Nat) :
    ((fromPacket layout port advance continuation localNameFits handler fuel).lower port).descriptionWords ≤
      442 * CallerStep.width layout + 245 + fuel * iterationWords layout port advance continuation handler := by
  have copied := distribute_words layout
  have returned := done_words layout
  have looped := fromState_words layout port advance continuation localNameFits handler fuel
  have bounds := sizes layout
  simp only [fromPacket, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute,
    Interactive.dispatch_descriptionWords]
  omega

variable {A : Type} (input : Representation w A) (initial : A → B ⊕ (Q × C))
    (initialCode : Realizer .unit input (CallerStep.next layout) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + layout.store.encoding.words < 2 ^ w)

def programWords (fuel : Nat) : Nat := descriptionWords initialCode.code + 26 * input.encoding.words +
  507 * CallerStep.width layout + 286 + fuel * iterationWords layout port advance continuation handler

theorem program_words (fuel : Nat) :
    ((program layout port advance continuation localNameFits handler input initial initialCode initialNameFits inputFits fuel).lower port).descriptionWords ≤
      programWords layout port advance continuation handler input initial initialCode fuel := by
  have copied := initialCode.retain_descriptionWords_le (by decide) layout.store layout.width initialNameFits inputFits (CallerStep.output layout).fits
  have looped := fromPacket_words layout port advance continuation localNameFits handler fuel
  have bounds := sizes layout
  simp only [program, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute, programWords]
  omega

section Acceptance
variable (handlerFits : (handler.lower port).DescriptionFits)
    (handlerNameFits : Interactive.savedBuffer port handler < 2 ^ w)

include handlerFits handlerNameFits in
theorem body_descriptionFits : ((body layout port advance continuation localNameFits handler).lower port).DescriptionFits :=
  (CallerStep.descriptionFits layout port advance continuation localNameFits handlerFits handlerNameFits).seq layout.width
    (.compute (route layout).description_fits)

include handlerFits handlerNameFits in
theorem fromState_descriptionFits (fuel : Nat) :
    ((fromState layout port advance continuation localNameFits handler fuel).lower port).DescriptionFits :=
  Interactive.loop_descriptionFits port _ _ _ _ fuel layout.width
    (body_descriptionFits layout port advance continuation localNameFits handler handlerFits handlerNameFits)
    (.compute (stop layout).description_fits) (CallerStep.output layout).fits (CallerStep.frame layout).fits

include handlerFits handlerNameFits in
theorem fromPacket_descriptionFits (fuel : Nat) :
    ((fromPacket layout port advance continuation localNameFits handler fuel).lower port).DescriptionFits :=
  WordIO.Code.DescriptionFits.seq layout.width (.compute (distribute layout).description_fits)
    (Interactive.dispatch_descriptionFits port _ _ _ _ layout.width
      (.compute (done layout).description_fits)
      (fromState_descriptionFits layout port advance continuation localNameFits handler handlerFits handlerNameFits fuel)
      (result layout).fits (CallerStep.frame layout).fits)

include handlerFits handlerNameFits in
theorem program_descriptionFits (fuel : Nat) :
    ((program layout port advance continuation localNameFits handler input initial initialCode initialNameFits inputFits fuel).lower port).DescriptionFits :=
  WordIO.Code.DescriptionFits.seq layout.width
    (.compute (initialCode.retain (by decide) layout.store layout.width initialNameFits inputFits (CallerStep.output layout).fits).description_fits)
    (fromPacket_descriptionFits layout port advance continuation localNameFits handler handlerFits handlerNameFits fuel)
end Acceptance

section Names
variable {slots : Nat} (room : 3 ≤ slots)
    (handlerNames : WordIO.NamesAccounted (handler.lower port) slots)
    (localNames : NamesAccounted continuation.code slots)

include room handlerNames localNames in
theorem body_names : WordIO.NamesAccounted ((body layout port advance continuation localNameFits handler).lower port) slots :=
  (CallerStep.names layout port advance continuation localNameFits handlerNames localNames).seq
    (WordIO.NamesAccounted.compute ((route_names layout).mono room))

include room handlerNames localNames in
theorem fromState_names (fuel : Nat) :
    WordIO.NamesAccounted ((fromState layout port advance continuation localNameFits handler fuel).lower port) slots :=
  Interactive.loop_names port (stop := .compute (stop layout).code)
    (body_names layout port advance continuation localNameFits handler room handlerNames localNames)
    (WordIO.NamesAccounted.compute ((stop_names layout).mono room)) _ _ fuel

include room handlerNames localNames in
theorem fromPacket_names (fuel : Nat) :
    WordIO.NamesAccounted ((fromPacket layout port advance continuation localNameFits handler fuel).lower port) slots :=
  (WordIO.NamesAccounted.compute ((distribute_names layout).mono room)).seq
    (Interactive.dispatch_names port (left := .compute (done layout).code)
      (WordIO.NamesAccounted.compute ((done_names layout).mono room))
      (fromState_names layout port advance continuation localNameFits handler room handlerNames localNames fuel) _ _)

include room handlerNames localNames in
theorem program_names (initialNames : NamesAccounted initialCode.code slots) (fuel : Nat) :
    WordIO.NamesAccounted ((program layout port advance continuation localNameFits handler input initial initialCode initialNameFits inputFits fuel).lower port) slots :=
  (WordIO.NamesAccounted.compute (Retain.names initialNames _ _ _)).seq
    (fromPacket_names layout port advance continuation localNameFits handler room handlerNames localNames fuel)
end Names

end CallerControl
end Signatures.Runtime.CaliperBackend
