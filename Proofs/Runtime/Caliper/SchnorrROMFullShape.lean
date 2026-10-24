import Proofs.Runtime.Caliper.SchnorrROMReplayExtractFullBounds

/-! The attacker-independent part of a Schnorr ROM caller: its state encoding
and declared local allowances. Every resource budget of the complete executed
solver is a function of this shape, the handler, the extractor primitives and
the query allowances alone, so the public DLog budget is fixed before the
attacker is chosen. The attacker supplies the local routines over the fixed
shape; the derived budgets then agree with the caller-indexed ones by `rfl`. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Full
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

structure Shape where
  State : Type
  state : Representation w State
  fits : 8 * (1 + state.encoding.words + (CallerPackets.request config).encoding.words +
    (CallerPackets.reply config).encoding.words + (ForgeryHash.forgery config).representation.encoding.words +
    config.handler.store.representation.encoding.words) < 2 ^ w

/-- Declared allowances for the attacker's own local code. -/
structure Limits where
  localTime : Nat
  initialTime : Nat
  localWords : Nat
  initialWords : Nat
  names : Nat

variable (shape : Shape config)
def Shape.layout := Pass.control config shape.state shape.fits
def Shape.width := CallerStep.width (shape.layout config)
def Shape.pending := CallerStep.pending (shape.layout config)

/-- Local caller routines over the fixed shape (`Pass.Caller` without its state fields). -/
structure Caller where
  advance : shape.State × CallerPackets.Reply config → (ForgeryHash.forgery config).Value ⊕ (CallerPackets.Request config × shape.State)
  continuation : Realizer .unit (CallerStep.resume (shape.layout config)) (CallerStep.next (shape.layout config)) advance
  localNameFits : continuation.savedBuffer < 2 ^ w
  initial : config.point.Value → (ForgeryHash.forgery config).Value ⊕ (CallerPackets.Request config × shape.State)
  initialization : Realizer .unit config.point.representation (CallerStep.next (shape.layout config)) initial
  initialNameFits : initialization.savedBuffer < 2 ^ w

variable (caller : Caller config shape)
def Caller.toPass : Pass.Caller config shape.State where
  state := shape.state
  fits := shape.fits
  advance := caller.advance
  continuation := caller.continuation
  localNameFits := caller.localNameFits
  initial := caller.initial
  initialization := caller.initialization
  initialNameFits := caller.initialNameFits

variable (limits : Limits)
structure Caller.Bounds : Prop where
  localTime : ∀ value, caller.continuation.time value ≤ limits.localTime
  initialTime : ∀ value, caller.initialization.time value ≤ limits.initialTime
  localWords : descriptionWords caller.continuation.code ≤ limits.localWords
  initialWords : descriptionWords caller.initialization.code ≤ limits.initialWords
  localNames : NamesAccounted caller.continuation.code limits.names
  initialNames : NamesAccounted caller.initialization.code limits.names
  localRoom : caller.continuation.code.memBound + 1 < 2 ^ w
  initialRoom : caller.initialization.code.memBound + 1 < 2 ^ w

def Caller.Bounds.localBudget (bounded : caller.Bounds config shape limits) :
    SchnorrROM.Caller.LocalBudget config ((caller.toPass config shape).routines config) where
  localTime := limits.localTime
  initialTime := limits.initialTime
  localWords := limits.localWords
  initialWords := limits.initialWords
  local_time := bounded.localTime
  initial_time := bounded.initialTime
  local_words := bounded.localWords
  initial_words := bounded.initialWords

section Budgets
variable [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G] [DecidableEq F] [Sub F] [Div F]
    (ops : Handler.Operations config) (budget : Handler.Budget config ops) (qH : Nat) (indexFits : qH + 1 < 2 ^ w)
    (arith : ReplayFork.Extract.Arithmetic config) (arithBudget : ReplayFork.Extract.Arithmetic.Budget config arith)

/-! The caller-indexed budget chain, restated over the shape. Each definition
copies the corresponding caller-indexed body with the caller's layout and local
budget replaced by `shape` and `limits`. -/
def callerTime (fuel : Nat) := CallerControl.timeBudget config.point.representation.encoding.words (shape.width config)
  (CallerHandler.timeBudget config ops budget) limits.localTime limits.initialTime fuel
def callerWords (fuel : Nat) := limits.initialWords + 26 * config.point.representation.encoding.words +
  507 * shape.width config + 286 +
  fuel * (CallerHandler.codeBudget config ops budget + limits.localWords + 742 * shape.width config + 389)
def finishTime (fuel : Nat) := callerTime config shape limits ops budget fuel + Terminal.timeBudget config (shape.pending config)
def finishWords (fuel : Nat) := callerWords config shape limits ops budget fuel + Terminal.codeBudget config (shape.pending config) + 1
def passTime (fuel : Nat) := 8 * (Pass.Initialization.output config).encoding.words + finishTime config shape limits ops budget fuel
def passWords (fuel : Nat) := 26 * (Pass.Initialization.output config).encoding.words + finishWords config shape limits ops budget fuel + 16
def firstTime (fuel : Nat) := passTime config shape limits ops budget fuel + ReplayFirst.selectorTime config ops qH indexFits budget
def firstWords (fuel : Nat) := passWords config shape limits ops budget fuel + ReplayFirst.selectorWords config ops qH indexFits budget + 2
def secondTime (fuel : Nat) := ReplaySecond.initializationTime config +
  (passTime config shape limits ops budget fuel +
    8 * (Pass.Initialization.input config).encoding.words + 8 * (ReplaySecond.first config).encoding.words +
    12 * (ReplaySecond.rawInput config).encoding.words)
def secondWords (fuel : Nat) := ReplaySecond.initializationWords config +
  passWords config shape limits ops budget fuel +
    26 * (Pass.Initialization.input config).encoding.words + 26 * (ReplaySecond.first config).encoding.words +
    39 * (ReplaySecond.rawInput config).encoding.words + 43
def selectedTime (fuel : Nat) := secondTime config shape limits ops budget fuel + ReplayMatch.timeBudget config ops qH indexFits budget
def selectedWords (fuel : Nat) := secondWords config shape limits ops budget fuel + ReplayMatch.codeBudget config ops qH indexFits budget + 2
def replayTime (fuel : Nat) := selectedTime config shape limits ops budget qH indexFits fuel + ReplayFork.finishTime config
def replayWords (fuel : Nat) := selectedWords config shape limits ops budget qH indexFits fuel + ReplayFork.finishWords config + 2
def guardTime (fuel : Nat) := Interactive.dispatchTime (w := w) .unit
  (ReplaySecond.rawInput config).encoding.words (ReplaySecond.rawInput config).encoding.words
  (replayTime config shape limits ops budget qH indexFits fuel) (8 * (ReplayFork.output config).encoding.words)
def guardWords (fuel : Nat) := replayWords config shape limits ops budget qH indexFits fuel +
  26 * (ReplayFork.output config).encoding.words + 52 * (ReplaySecond.rawInput config).encoding.words + 55
def afterTime (fuel : Nat) := ReplayChallenge.Checked.timeBudget config + guardTime config shape limits ops budget qH indexFits fuel
def afterWords (fuel : Nat) := ReplayChallenge.Checked.codeBudget config + guardWords config shape limits ops budget qH indexFits fuel + 1
def branchTime (fuel : Nat) := Interactive.dispatchTime (w := w) .unit
  (ReplayChallenge.input config).encoding.words (ReplayChallenge.input config).encoding.words
  (8 * (ReplayFork.output config).encoding.words) (afterTime config shape limits ops budget qH indexFits fuel)
def branchWords (fuel : Nat) := afterWords config shape limits ops budget qH indexFits fuel +
  26 * (ReplayFork.output config).encoding.words + 52 * (ReplayChallenge.input config).encoding.words + 55
def forkTime (fuel : Nat) := firstTime config shape limits ops budget qH indexFits fuel + branchTime config shape limits ops budget qH indexFits fuel
def forkWords (fuel : Nat) := firstWords config shape limits ops budget qH indexFits fuel + branchWords config shape limits ops budget qH indexFits fuel + 1
def initializedTime (fuel : Nat) := 8 * (Pass.Initialization.input config).encoding.words + forkTime config shape limits ops budget qH indexFits fuel
def initializedWords (fuel : Nat) := 26 * (Pass.Initialization.input config).encoding.words + 16 + forkWords config shape limits ops budget qH indexFits fuel

/-- Complete solver budgets: controller, then extractor. -/
def timeBudget (fuel : Nat) := initializedTime config shape limits ops budget qH indexFits fuel +
  ReplayFork.Extract.timeBudget config arith arithBudget
def codeBudget (fuel : Nat) := initializedWords config shape limits ops budget qH indexFits fuel +
  ReplayFork.Extract.codeBudget config arith arithBudget + 1
def nameBudget := ReplayFork.Extract.fullNameBudget config ops arith limits.names
def memoryBudget (fuel : Nat) := 5 * codeBudget config shape limits ops budget qH indexFits arith arithBudget fuel +
  4 * nameBudget config limits ops arith + 3 + (Pass.Initialization.points config).representation.encoding.words +
  timeBudget config shape limits ops budget qH indexFits arith arithBudget fuel

variable (bounded : caller.Bounds config shape limits)
omit [DecidableEq F] in
theorem time_eq (fuel : Nat) :
    ReplayFork.Extract.fullTimeBudget config (caller.toPass config shape) ops qH indexFits budget
      (bounded.localBudget config shape caller limits) arith arithBudget fuel =
    timeBudget config shape limits ops budget qH indexFits arith arithBudget fuel := rfl
omit [DecidableEq F] in
theorem code_eq (fuel : Nat) :
    ReplayFork.Extract.fullCodeBudget config (caller.toPass config shape) ops qH indexFits budget
      (bounded.localBudget config shape caller limits) arith arithBudget fuel =
    codeBudget config shape limits ops budget qH indexFits arith arithBudget fuel := rfl
end Budgets

end Signatures.Runtime.CaliperBackend.SchnorrROM.Full
