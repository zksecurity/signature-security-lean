import Caliper.Core

/-! Caliper programs with a finite interface of cryptographic routine calls.

Local computation is literal Caliper syntax. A call expands to the selected
Caliper routine at code-generation time. Execution and all resource measures
are therefore those of the lowered Caliper program, including the actual tape
cursor and buffer capacities. No arbitrary Lean function is executable here.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

/-- `Call` is the signature of the cryptographic library, including its operands. -/
inductive Program (w : Nat) (Call : Type) where
  | words (code : Stmt w)
  | call (operation : Call)
  | seq (first second : Program w Call)
  | branch (condition : Reg) (yes no : Program w Call)
  | loop (guard : Program w Call) (condition : Reg) (body : Program w Call)

/-- Actual Caliper routine implementations, selected once for an entire program. -/
abbrev Library (w : Nat) (Call : Type) := Call → Stmt w

variable {w : Nat} {Call : Type}

def Program.lower (library : Library w Call) : Program w Call → Stmt w
  | .words code => code
  | .call operation => library operation
  | .seq first second => .seq (first.lower library) (second.lower library)
  | .branch condition yes no => .ifNZ condition (yes.lower library) (no.lower library)
  | .loop guard condition body => .whileNZ (guard.lower library) condition (body.lower library)

/-- The hybrid machine is executed by Caliper itself. The memory indices are
net and peak *buffer* memory; register and stored-code footprints are separate. -/
abbrev Exec (cost : CostModel) (tape : RandomTape w) (library : Library w Call)
    (program : Program w Call) := Caliper.Exec cost tape (program.lower library)

/-- Executable evaluation also uses Caliper's interpreter, with its observable
fuel exhaustion and invalid-memory-access behavior. -/
def Program.run (cost : CostModel) (tape : RandomTape w) (library : Library w Call)
    (fuel : Nat) (program : Program w Call) (state : State w) :=
  Caliper.run cost tape fuel (program.lower library) state

end Signatures.Runtime.CaliperBackend
