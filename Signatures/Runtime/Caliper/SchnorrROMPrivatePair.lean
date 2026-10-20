import Signatures.Runtime.Caliper.SchnorrROMPrivateServiceBuffers

/-! Two private scalar samples on one shared replay tape. The first scalar is
saved while the second sampler executes. All permutations and retained copies
are machine instructions; only byte-identical subtype views are mathematical. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Pair
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F C : Type} (layout : Layouts w F C)

def unpack (value : (Reply.scalarOutput layout.tape).Value) : layout.tape.scalar.Value × Store layout :=
  (⟨value.val.1, value.property.1⟩, ⟨value.val.2, value.property.2⟩)

theorem outputFits : layout.tape.scalar.representation.encoding.words +
    (Reply.scalarOutput layout.tape).representation.encoding.words < 2 ^ w := by
  have := layout.fits
  change layout.tape.scalar.representation.encoding.words +
    (layout.tape.scalar.representation.encoding.words + (Read.tapes layout.tape).representation.encoding.words) < 2 ^ w
  omega

def output := layout.tape.scalar.prod (Reply.scalarOutput layout.tape) (outputFits layout)
def pack (first : layout.tape.scalar.Value) (second : (Reply.scalarOutput layout.tape).Value) : (output layout).Value :=
  ⟨(first.val, second.val), first.property, second.property⟩

def prepare : Realizer .unit (Reply.scalarOutput layout.tape).representation
    ((Read.tapes layout.tape).representation.prod layout.tape.scalar.representation (by
      have := (Reply.scalarOutput layout.tape).representation.fits
      change layout.tape.scalar.representation.encoding.words + (Read.tapes layout.tape).representation.encoding.words < 2 ^ w at this
      omega)) (fun value => ((unpack layout value).2, (unpack layout value).1)) :=
  (Pairing.swap .unit (by decide) layout.tape.scalar.representation (Read.tapes layout.tape).representation
    layout.tape.wordFits (Reply.scalarOutput layout.tape).representation.fits).viewInput
      (Reply.scalarOutput layout.tape).representation (unpack layout) (fun _ => rfl)

def finish : Realizer .unit
    ((Reply.scalarOutput layout.tape).representation.prod layout.tape.scalar.representation (by have := outputFits layout; omega))
    (output layout).representation (fun value => pack layout value.2 value.1) :=
  (Pairing.swap .unit (by decide) (Reply.scalarOutput layout.tape).representation layout.tape.scalar.representation
    layout.tape.wordFits (by have := outputFits layout; omega)).viewOutput (output layout).representation
      (fun value => pack layout value.2 value.1) (fun _ => rfl)

variable [Zero F] (caller : Caller layout) (zeroValid : layout.tape.scalar.valid 0)

def retained (fuel : Nat) : Interactive.Code w :=
  Interactive.retain (Service.code layout caller zeroValid fuel)
    (Interactive.savedBuffer (Fresh.port layout.tape) (Service.code layout caller zeroValid fuel))
    (Read.tapes layout.tape).representation.encoding.words (Reply.scalarOutput layout.tape).representation.encoding.words
    layout.tape.scalar.representation.encoding.words
def continuation (fuel : Nat) : Interactive.Code w :=
  .seq (.compute (prepare layout).code) (.seq (retained layout caller zeroValid fuel) (.compute (finish layout).code))
def code (fuel : Nat) : Interactive.Code w :=
  .seq (Service.code layout caller zeroValid fuel) (continuation layout caller zeroValid fuel)

def ready (fuel : Nat) (saved : Store layout) := Service.ready layout (fuel + fuel) saved
def nextReady (fuel : Nat) (first : (Reply.scalarOutput layout.tape).Value) :=
  Service.ready layout fuel (unpack layout first).2
def source (fuel : Nat) (saved : Store layout) : ProbComp (output layout).Value := do
  let first ← Service.source layout caller zeroValid fuel saved
  (pack layout (unpack layout first).1) <$> Service.source layout caller zeroValid fuel (unpack layout first).2

omit [Zero F] in
theorem first_ready (fuel : Nat) (saved : Store layout) (valid : ready layout fuel saved) :
    Service.ready layout fuel saved := by
  change saved.val.1.length + (fuel + fuel) ≤ layout.tape.capacity at valid
  change saved.val.1.length + fuel ≤ layout.tape.capacity
  omega

theorem second_ready (fuel : Nat) (saved : Store layout) (valid : ready layout fuel saved)
    (first : (Reply.scalarOutput layout.tape).Value)
    (reached : first ∈ support (Service.source layout caller zeroValid fuel saved)) : nextReady layout fuel first :=
  Service.reserved_after layout caller zeroValid fuel fuel saved valid first reached

theorem continuation_refines (fuel : Nat) :
    Interactive.RefinesOn (nextReady layout fuel) (Fresh.port layout.tape) .unit
      (Reply.scalarOutput layout.tape).representation (output layout).representation
      (fun first => (pack layout (unpack layout first).1) <$>
        Service.source layout caller zeroValid fuel (unpack layout first).2)
      (continuation layout caller zeroValid fuel) := by
  have saved := (Service.refines layout caller zeroValid fuel).retain (by decide) layout.tape.scalar.representation
    layout.tape.wordFits (by
      have := (Reply.scalarOutput layout.tape).representation.fits
      change layout.tape.scalar.representation.encoding.words + (Read.tapes layout.tape).representation.encoding.words < 2 ^ w at this
      omega) (by have := outputFits layout; omega)
  have finished := saved.seq
    ((Interactive.Refines.compute (Fresh.port layout.tape) .unit (finish layout)).on (fun _ => True)) (by intros; trivial)
  have prepared := ((Interactive.Refines.compute (Fresh.port layout.tape) .unit (prepare layout)).on
    (nextReady layout fuel)).seq finished (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact valid)
  convert prepared using 1
  · funext value
    simp only [pure_bind, bind_pure_comp, Functor.map_map]
  · rfl

theorem refines (fuel : Nat) : Interactive.RefinesOn (ready layout fuel) (Fresh.port layout.tape) .unit
    (Read.tapes layout.tape).representation (output layout).representation
    (source layout caller zeroValid fuel) (code layout caller zeroValid fuel) := by
  have first : Interactive.RefinesOn (ready layout fuel) (Fresh.port layout.tape) .unit
      (Read.tapes layout.tape).representation (Reply.scalarOutput layout.tape).representation
      (Service.source layout caller zeroValid fuel) (Service.code layout caller zeroValid fuel) :=
    fun tape saved valid before holds => Service.refines layout caller zeroValid fuel tape saved
      (first_ready layout fuel saved valid) before holds
  exact first.seq (continuation_refines layout caller zeroValid fuel) (second_ready layout caller zeroValid fuel)

theorem reserved_after (fuel reserve : Nat) (saved : Store layout)
    (room : PrivateHandler.Reserved layout.tape (fuel + fuel + reserve) saved)
    (answer : (output layout).Value) (reached : answer ∈ support (source layout caller zeroValid fuel saved)) :
    answer.val.2.2.1.length + reserve ≤ layout.tape.capacity := by
  simp only [source, support_bind, Set.mem_iUnion, support_map, Set.mem_image] at reached
  obtain ⟨first, supported, second, secondSupported, rfl⟩ := reached
  have remaining := Service.reserved_after layout caller zeroValid fuel (fuel + reserve) saved
    (by simpa only [Nat.add_assoc] using room) first supported
  exact Service.reserved_after layout caller zeroValid fuel reserve (unpack layout first).2 remaining second secondSupported

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Pair
