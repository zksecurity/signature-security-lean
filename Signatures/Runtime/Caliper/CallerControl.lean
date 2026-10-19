import Signatures.Runtime.Caliper.CallerStepBounds

/-! Generated bounded caller control. A stored result returns immediately; a
stored pending request enters the handler/continuation loop. At the fuel limit
the pending request and state are retained in the output, so cutoff is observable
and cannot be confused with a successful return. Initialization runs once while
the private store is preserved by charged copying. -/

namespace Signatures.Runtime.CaliperBackend.CallerControl
open Caliper OracleComp OracleSpec

variable {w : Nat} {C Q R B S : Type} (layout : CallerStep.Layouts w C Q R B S)

abbrev Packet (C Q B S : Type) := (B ⊕ (Q × C)) × S
abbrev Frame (C Q S : Type) := (Q × C) × S

def returned (value : B × S) : Packet C Q B S := (.inl value.1, value.2)
def suspended (value : Frame C Q S) : Packet C Q B S := (.inr value.1, value.2)
def select (value : Packet C Q B S) : Packet C Q B S ⊕ Frame C Q S :=
  match value.1 with
  | .inl _ => .inl value
  | .inr pending => .inr (pending, value.2)

/-- Observation of a completed run. This is a mathematical observation of the
stored tag, not an uncharged instruction that converts machine memory. -/
def answer (value : Packet C Q B S) : Option B × S :=
  (value.1.elim some (fun _ => none), value.2)

def result : Representation w (B × S) := layout.result.prod layout.store (by have := layout.fits; omega)
def choice : Representation w ((B × S) ⊕ Frame C Q S) :=
  SumContext.output layout.result (CallerStep.pending layout) layout.store layout.width (CallerStep.output layout).fits
def iteration : Representation w (Packet C Q B S ⊕ Frame C Q S) :=
  (CallerStep.output layout).sum (CallerStep.frame layout) (width_pos layout.width) (by
    have := layout.fits
    change 1 + max
      (1 + max layout.result.encoding.words (layout.request.encoding.words + layout.state.encoding.words) + layout.store.encoding.words)
      (layout.request.encoding.words + layout.state.encoding.words + layout.store.encoding.words) < 2 ^ w
    omega)

def distribute : Realizer .unit (CallerStep.output layout) (choice layout) SumContext.view :=
  SumContext.distribute layout.result (CallerStep.pending layout) layout.store layout.width (CallerStep.output layout).fits

def done : Realizer .unit (result layout) (CallerStep.output layout) returned :=
  (inlRealizer .unit (by decide) layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits).retain
    (by decide) layout.store layout.width (by
      have bounded := (inl_names layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits).buffers
      dsimp only [Realizer.savedBuffer]
      have := layout.width
      omega)
    (result layout).fits (CallerStep.output layout).fits

def stop : Realizer .unit (CallerStep.frame layout) (CallerStep.output layout) suspended :=
  (inrRealizer .unit (by decide) layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits).retain
    (by decide) layout.store layout.width (by
      have bounded := (inr_names layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits).buffers
      dsimp only [Realizer.savedBuffer]
      have := layout.width
      omega)
    (CallerStep.frame layout).fits (CallerStep.output layout).fits

def route : Realizer .unit (CallerStep.output layout) (iteration layout) select :=
  ((distribute layout).then
    (branchRealizer .unit (by decide) (result layout) (CallerStep.frame layout) (iteration layout)
      ((done layout).then (inlRealizer .unit (by decide) (CallerStep.output layout) (CallerStep.frame layout)
        layout.width (iteration layout).fits))
      (inrRealizer .unit (by decide) (CallerStep.output layout) (CallerStep.frame layout)
        layout.width (iteration layout).fits)
      layout.width (choice layout).fits)).viewOutput (iteration layout) select (by
        intro value
        rcases value with ⟨value | pending, saved⟩ <;> rfl)

variable {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    (advance : C × R → B ⊕ (Q × C))
    (continuation : Realizer .unit (CallerStep.resume layout) (CallerStep.next layout) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)
    (handler : Interactive.Code w)

def body : Interactive.Code w :=
  .seq (CallerStep.code layout port advance continuation localNameFits handler) (.compute (route layout).code)

def fromState (fuel : Nat) : Interactive.Code w :=
  Interactive.loop (body layout port advance continuation localNameFits handler) (.compute (stop layout).code)
    (CallerStep.output layout).encoding.words (CallerStep.frame layout).encoding.words fuel

def fromPacket (fuel : Nat) : Interactive.Code w :=
  .seq (.compute (distribute layout).code)
    (Interactive.dispatch (.compute (done layout).code)
      (fromState layout port advance continuation localNameFits handler fuel)
      (result layout).encoding.words (CallerStep.frame layout).encoding.words)

variable {A : Type} (input : Representation w A) (initial : A → B ⊕ (Q × C))
    (initialCode : Realizer .unit input (CallerStep.next layout) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + layout.store.encoding.words < 2 ^ w)

def program (fuel : Nat) : Interactive.Code w :=
  .seq (.compute (initialCode.retain (by decide) layout.store layout.width initialNameFits inputFits (CallerStep.output layout).fits).code)
    (fromPacket layout port advance continuation localNameFits handler fuel)

section Source
variable (advance : C × R → B ⊕ (Q × C)) (H : Q × S → OracleComp spec (R × S))

def bodySource (value : Frame C Q S) : OracleComp spec (Packet C Q B S ⊕ Frame C Q S) :=
  select <$> CallerStep.denote advance H value

def denote (fuel : Nat) : Frame C Q S → OracleComp spec (Packet C Q B S) :=
  BackendProgram.loopDenote (bodySource advance H) (fun value => pure (suspended value)) fuel

def start (fuel : Nat) (value : Packet C Q B S) : OracleComp spec (Packet C Q B S) :=
  match value.1 with
  | .inl _ => pure value
  | .inr pending => denote advance H fuel (pending, value.2)

@[simp] theorem start_returned (fuel : Nat) (value : B × S) : start advance H fuel (returned value) = pure (returned value) := rfl
@[simp] theorem start_suspended (fuel : Nat) (value : Frame C Q S) : start advance H fuel (suspended value) = denote advance H fuel value := rfl
@[simp] theorem denote_zero (value : Frame C Q S) : denote advance H 0 value = pure (suspended value) := rfl

theorem denote_succ (fuel : Nat) (value : Frame C Q S) : denote advance H (fuel + 1) value =
    H (value.1.1, value.2) >>= fun reply => start advance H fuel (advance (value.1.2, reply.1), reply.2) := by
  simp only [denote, BackendProgram.loopDenote, bodySource, CallerStep.denote, bind_map_left]
  congr 1
  funext reply
  cases advance (value.1.2, reply.1) <;> simp [select, start, denote]

def Valid (invariant : Nat → Frame C Q S → Prop) (fuel : Nat) (value : Packet C Q B S) : Prop :=
  match value.1 with
  | .inl _ => True
  | .inr pending => invariant fuel (pending, value.2)

end Source

end Signatures.Runtime.CaliperBackend.CallerControl
