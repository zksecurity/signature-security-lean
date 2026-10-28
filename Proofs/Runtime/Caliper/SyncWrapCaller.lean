import Proofs.Runtime.Caliper.SyncWrapBounds

/-! The wrapper as a weighted caller over the outer layouts. The step and initialization
implementations are read at the caller's packet representations, which share bytes with the
wrapper's layouts, and their budgets become the caller's bounds. -/
namespace Signatures.Runtime.CaliperBackend.SyncWrap
open Caliper BoundedSource WeightedFull

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key scalar : Ty Atom} {M G PK A : Type} [Zero (scalar.Value base)]
  {core : Core w (key.Value base) M G (scalar.Value base) PK A} (routines : Routines core) (caller : SharedCaller core.inner)
  (wrapper : Wrapper core) (outLe : wrapper.outer.good.forgery.representation.encoding.words ≤ core.outWords)
  {finishFn : core.forgeryIn.Value × (core.scalar.Value × List (Unit ⊕ scalar.Value base)) →
    M × (scalar.Value base × (List (scalar.Value base) × List (scalar.Value base)))}
  (finish : Implementation .unit core.finalInput wrapper.outer.good.forgery finishFn)
  (callerReserve : caller.continuation.code.memBound + 50 < 2 ^ w)
  (initialReserve : caller.initialCode.code.memBound + 50 < 2 ^ w)

namespace Wrapper

/-- The wrapper's answer, read as the outer caller's. -/
def toNext (value : (core.output wrapper.outer.good.forgery outLe).Value) :
    wrapper.outer.good.forgery.Value ⊕ (wrapper.outer.good.Request × core.wrapper.Value) :=
  match value with
  | ⟨.inl forged, valid⟩ => .inl ⟨forged, valid⟩
  | ⟨.inr (request, state), valid⟩ => .inr (request, ⟨state, valid.2⟩)

theorem toNext_bytes (value : (core.output wrapper.outer.good.forgery outLe).Value) :
    (CallerStep.next wrapper.outer.good.control).encoding.encode (wrapper.toNext outLe value) =
      (core.output wrapper.outer.good.forgery outLe).representation.encoding.encode value := by
  rcases value with ⟨forged | ⟨request, state⟩, valid⟩ <;> rfl

/-- The outer caller's step. -/
def advance (value : core.wrapper.Value × wrapper.outer.good.Reply) :
    wrapper.outer.good.forgery.Value ⊕ (wrapper.outer.good.Request × core.wrapper.Value) :=
  wrapper.toNext outLe ⟨core.advanceFn (finishFn := finishFn) routines caller (value.1.val, value.2),
    (core.advanceImpl routines caller wrapper.outer.good.forgery outLe finish callerReserve).preserves _ ⟨value.1.property, trivial⟩⟩

/-- The step, read at the caller's packet representations. -/
def continuation : Realizer .unit (CallerStep.resume wrapper.outer.good.control) (CallerStep.next wrapper.outer.good.control)
    (wrapper.advance routines caller outLe finish callerReserve) :=
  ((core.advanceImpl routines caller wrapper.outer.good.forgery outLe finish callerReserve).program.viewInput
    (CallerStep.resume wrapper.outer.good.control) (fun value => ⟨(value.1.val, value.2), ⟨value.1.property, trivial⟩⟩) (fun _ => rfl)).viewOutput
    (CallerStep.next wrapper.outer.good.control) _ (fun _ => wrapper.toNext_bytes outLe _)

/-- The outer caller's first step. -/
def initial (value : core.key.Value) : wrapper.outer.good.forgery.Value ⊕ (wrapper.outer.good.Request × core.wrapper.Value) :=
  wrapper.toNext outLe ⟨core.initialFn routines caller value,
    (core.initialImpl routines caller wrapper.outer.good.forgery outLe initialReserve).preserves _ trivial⟩

def initialCode : Realizer .unit wrapper.outer.goodSetup.key.representation (CallerStep.next wrapper.outer.good.control)
    (wrapper.initial routines caller outLe initialReserve) :=
  ((core.initialImpl routines caller wrapper.outer.good.forgery outLe initialReserve).program.viewInput
    wrapper.outer.goodSetup.key.representation (fun value => ⟨value, trivial⟩) (fun _ => rfl)).viewOutput
    (CallerStep.next wrapper.outer.good.control) _ (fun _ => wrapper.toNext_bytes outLe _)

variable (innerBounds : Caller.Bounds core.inner.good core.inner.goodSetup caller)
  (finishTime finishWords finishSlots : Nat) (finishBound : finish.BoundedBy finishTime finishWords)
  (finishNames : NamesAccounted finish.program.code finishSlots)
  (reserve : core.slotsAll routines caller innerBounds finishSlots + 3000000 * core.unitW routines caller innerBounds finishWords + 2 < 2 ^ w)

include finishBound finishNames reserve in
/-- The wrapper as a caller over the outer layouts. -/
def toCaller : SharedCaller wrapper.outer where
  advance := wrapper.advance routines caller outLe finish callerReserve
  continuation := wrapper.continuation routines caller outLe finish callerReserve
  localNameFits := by
    change max 2 (core.advanceImpl routines caller wrapper.outer.good.forgery outLe finish callerReserve).program.code.memBound < 2 ^ w
    have names := (core.advanceImpl_names routines caller innerBounds wrapper.outer.good.forgery outLe finish finishSlots finishNames callerReserve).buffers
    have words := (core.advanceImpl_boundedBy routines caller innerBounds wrapper.outer.good.forgery outLe finish finishTime finishWords finishBound
      callerReserve).code_le
    omega
  initial := wrapper.initial routines caller outLe initialReserve
  initialCode := wrapper.initialCode routines caller outLe initialReserve
  initialNameFits := by
    change max 2 (core.initialImpl routines caller wrapper.outer.good.forgery outLe initialReserve).program.code.memBound < 2 ^ w
    have names := (core.initialImpl_names routines caller innerBounds wrapper.outer.good.forgery outLe finishSlots initialReserve).buffers
    have words := (core.initialImpl_boundedBy routines caller innerBounds wrapper.outer.good.forgery outLe finishTime finishWords initialReserve).code_le
    omega

/-- The outer caller's budgets: multiples of the unit. -/
def bounds : Caller.Bounds wrapper.outer.good wrapper.outer.goodSetup
    (wrapper.toCaller routines caller outLe finish callerReserve initialReserve innerBounds finishTime finishWords finishSlots finishBound finishNames reserve) where
  step := ⟨3000000 * core.unitT routines caller innerBounds finishTime, 3000000 * core.unitW routines caller innerBounds finishWords⟩
  initial := ⟨900000 * core.unitT routines caller innerBounds finishTime, 900000 * core.unitW routines caller innerBounds finishWords⟩
  localTime _ := (core.advanceImpl_boundedBy routines caller innerBounds wrapper.outer.good.forgery outLe finish finishTime finishWords finishBound
    callerReserve).time_le _
  initialTime _ := (core.initialImpl_boundedBy routines caller innerBounds wrapper.outer.good.forgery outLe finishTime finishWords initialReserve).time_le _
  localWords := (core.advanceImpl_boundedBy routines caller innerBounds wrapper.outer.good.forgery outLe finish finishTime finishWords finishBound
    callerReserve).code_le
  initialWords := (core.initialImpl_boundedBy routines caller innerBounds wrapper.outer.good.forgery outLe finishTime finishWords initialReserve).code_le
  slots := core.slotsAll routines caller innerBounds finishSlots
  localNames := core.advanceImpl_names routines caller innerBounds wrapper.outer.good.forgery outLe finish finishSlots finishNames callerReserve
  initialNames := core.initialImpl_names routines caller innerBounds wrapper.outer.good.forgery outLe finishSlots initialReserve

end Wrapper

end Signatures.Runtime.CaliperBackend.SyncWrap
