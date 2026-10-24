import Proofs.Runtime.Caliper.SchnorrROMPrivateHandler
import Proofs.Runtime.Caliper.CallerExecution
import Proofs.Runtime.Caliper.CallerPresentation

/-! Compile an adaptive scalar sampler from its local initialization and reply
transition. Every uniform query runs the constructed private replay handler.
The source tree and oracle machine are derived from those local transitions;
the only capacity invariant is a reservation for the remaining query count. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler
open Caliper BoundedSource OracleComp OracleSpec

structure Layouts (w : Nat) (F C : Type) where
  tape : SchnorrROMTape.Layouts w F
  state : Representation w C
  fits : 8 * (1 + state.encoding.words + 1 + 2 + tape.scalar.representation.encoding.words +
    (Read.tapes tape).representation.encoding.words) < 2 ^ w

variable {w : Nat} {F C : Type} (layout : Layouts w F C)
abbrev Request := PrivateHandler.Request layout.tape
abbrev Response := PrivateHandler.Response layout.tape
abbrev Store := PrivateHandler.Store layout.tape
abbrev Head := layout.tape.scalar.Value ⊕ (Request layout × C)

def step : CallerStep.Layouts w C (Request layout) (Response layout) layout.tape.scalar.Value (Store layout) where
  state := layout.state
  request := (Reply.range layout.tape).representation
  reply := (PrivateHandler.response layout.tape).representation
  result := layout.tape.scalar.representation
  store := (Read.tapes layout.tape).representation
  fits := layout.fits
  width := layout.tape.wordFits

structure Caller where
  initial : layout.tape.unit.Value → Head layout
  advance : C × Response layout → Head layout
  initialCode : Realizer .unit layout.tape.unit.representation (CallerStep.next (step layout)) initial
  continuation : Realizer .unit (CallerStep.resume (step layout)) (CallerStep.next (step layout)) advance
  initialFits : initialCode.savedBuffer < 2 ^ w
  localFits : continuation.savedBuffer < 2 ^ w

theorem inputFits : layout.tape.unit.representation.encoding.words + (Read.tapes layout.tape).representation.encoding.words < 2 ^ w := by
  change 0 + _ < _
  simpa using (Read.tapes layout.tape).representation.fits
def input := layout.tape.unit.representation.prod (Read.tapes layout.tape).representation (inputFits layout)
def invariant (calls : Nat) (value : CallerControl.Frame C (Request layout) (Store layout)) : Prop :=
  PrivateHandler.Reserved layout.tape calls value.2
def admissible (fuel : Nat) (value : layout.tape.unit.Value × Store layout) : Prop :=
  PrivateHandler.Reserved layout.tape fuel value.2

def representReply (q : Request layout) (answer : Fin (q.val + 1)) : Response layout :=
  ⟨(q.val, answer.val), ⟨q.property, by
    change answer.val < 2 ^ w
    have bound : q.val < 2 ^ w - 2 := q.property
    have := answer.isLt
    omega⟩, Nat.le_of_lt_succ answer.isLt⟩

theorem representReply_eq (q : Request layout) (represented : Response layout) (original : Fin (q.val + 1))
    (related : PrivateHandler.replyMatches layout.tape q represented original) :
    represented = representReply layout q original := Subtype.ext related

variable (caller : Caller layout)

def Terminates (fuel : Nat) : Prop := ∀ value,
  CallerMachine.Terminates (spec := unifSpec) Subtype.val (representReply layout) caller.advance fuel (caller.initial value)
noncomputable def original (fuel : Nat) (terminates : Terminates layout caller fuel) :=
  CallerMachine.sourceOfCaller (spec := unifSpec) Subtype.val (representReply layout) caller.advance caller.initial fuel terminates

theorem initial_valid (fuel : Nat) (value : layout.tape.unit.Value × Store layout)
    (valid : admissible layout fuel value) :
    CallerControl.Valid (invariant layout) fuel (caller.initial value.1, value.2) := by
  cases caller.initial value.1 with
  | inl _ => trivial
  | inr _ => exact valid

variable [Zero F] (zeroValid : layout.tape.scalar.valid 0)

def code (fuel : Nat) := CallerControl.program (step layout) (Fresh.port layout.tape)
  caller.advance caller.continuation caller.localFits (PrivateQuery.code layout.tape zeroValid)
  layout.tape.unit.representation caller.initial caller.initialCode caller.initialFits (inputFits layout) fuel
def source (fuel : Nat) (value : layout.tape.unit.Value × Store layout) :=
  CallerControl.start caller.advance (PrivateHandler.source layout.tape zeroValid) fuel (caller.initial value.1, value.2)

theorem preserves (remaining : Nat) (value : CallerControl.Frame C (Request layout) (Store layout))
    (valid : invariant layout (remaining + 1) value) (answer : Response layout × Store layout)
    (reached : answer ∈ support (PrivateHandler.source layout.tape zeroValid (value.1.1, value.2))) :
    CallerControl.Valid (invariant layout) remaining (caller.advance (value.1.2, answer.1), answer.2) := by
  have reserved := PrivateHandler.reserved_after layout.tape zeroValid (value.1.1, value.2) valid answer reached
  cases caller.advance (value.1.2, answer.1) with
  | inl _ => trivial
  | inr _ => exact reserved

theorem refines (fuel : Nat) : Interactive.RefinesOn (admissible layout fuel) (Fresh.port layout.tape) .unit
    (input layout) (CallerStep.output (step layout)) (source layout caller zeroValid fuel) (code layout caller zeroValid fuel) :=
  CallerControl.program_refines (step layout) (Fresh.port layout.tape) caller.advance caller.continuation caller.localFits
    (invariant layout) (PrivateHandler.ready layout.tape) (PrivateHandler.refines layout.tape zeroValid)
    (fun _ value valid => PrivateHandler.ready_of_reserved layout.tape (value.1.1, value.2) valid)
    (preserves layout caller zeroValid) layout.tape.unit.representation caller.initial caller.initialCode caller.initialFits
    (inputFits layout) fuel (admissible layout fuel) (initial_valid layout caller fuel)

theorem observe_source (fuel : Nat) (terminates : Terminates layout caller fuel)
    (tape : RandomTape w) (value : layout.tape.unit.Value × Store layout) (valid : admissible layout fuel value)
    (before : State w) (holds : (input layout).Holds value before) :
    (fun result => CallerMachine.observe (PrivateHandler.stored layout.tape) <$>
      Interactive.observe (CallerStep.output (step layout)) result) <$>
        (code layout caller zeroValid fuel).execute (Fresh.port layout.tape) .unit tape before =
      (fun result => some (some result.1, result.2)) <$>
        (simulateQ Schnorr.RawTape.Private.oracle (original layout caller fuel terminates value.1)).run
          (PrivateHandler.stored layout.tape value.2) := by
  apply CallerMachine.program_observe_source
    (CallerMachine.ofCaller (spec := unifSpec) Subtype.val (representReply layout) caller.advance caller.initial)
    Subtype.val Sum.inr (PrivateHandler.stored layout.tape) (PrivateHandler.replyMatches layout.tape)
    caller.advance (PrivateHandler.source layout.tape zeroValid) Schnorr.RawTape.Private.oracle (invariant layout)
    (fun _ value valid => PrivateHandler.synchronizes layout.tape zeroValid (value.1.1, value.2)
      (PrivateHandler.ready_of_reserved layout.tape (value.1.1, value.2) valid))
    (fun _ q c _ _ next view represented answer related =>
      CallerMachine.ofCaller_advance _ _ _ _ q c next view represented answer (representReply_eq layout q represented answer related))
    (preserves layout caller zeroValid) (step layout) (Fresh.port layout.tape) caller.continuation caller.localFits
    (PrivateQuery.code layout.tape zeroValid) (PrivateHandler.ready layout.tape) (PrivateHandler.refines layout.tape zeroValid)
    (fun _ value valid => PrivateHandler.ready_of_reserved layout.tape (value.1.1, value.2) valid)
    layout.tape.unit.representation caller.initial caller.initialCode caller.initialFits (inputFits layout)
    fuel (admissible layout fuel) (initial_valid layout caller fuel) id
    (fun value _ => CallerMachine.ofCaller_matches _ _ _ _ (caller.initial value.1))
    (original layout caller fuel terminates) (CallerMachine.ofCaller_implements _ _ _ _ _ terminates)
    tape value valid before holds

/-- Relating the caller's local sampling algorithm to the specified scalar
sampler is enough: its entire adaptive replay then equals `privateImpl`.
This is exact computation equality, rather than only a uniform output law. -/
theorem scalar_source [SampleableType F] (fuel : Nat) (terminates : Terminates layout caller fuel)
    (value : layout.tape.unit.Value)
    (samples : Subtype.val <$> original layout caller fuel terminates value = ($ᵗ F : ProbComp F))
    (state : Schnorr.RawTape.State F) :
    (fun result => (result.1.val, result.2)) <$>
      (simulateQ Schnorr.RawTape.Private.oracle (original layout caller fuel terminates value)).run state =
        simulateQ _root_.Schnorr.LazyROM.sample
          ((simulateQ Schnorr.RawTape.oracle (Schnorr.privateImpl (.inr ()))).run state) := by
  have same := congrArg (fun main : ProbComp F => (simulateQ Schnorr.RawTape.Private.oracle main).run state) samples
  simp only [simulateQ_map, StateT.run_map] at same
  exact same.trans (Schnorr.RawTape.Private.scalar_source state)

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler
