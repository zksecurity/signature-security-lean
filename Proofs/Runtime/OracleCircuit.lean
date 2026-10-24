import Proofs.Runtime.CircuitExecution
import Proofs.Runtime.Program

/-!
A raw-bit adversary language, in contrast to CryptoOp's opaque group values.
Every Boolean circuit can be embedded, with its actual compiled cell cost.
Oracle request/reply bits remain external here; a signature-specific codec,
fixed-tape reduction, and end-to-end hardness theorem still have to be connected.
This file does not claim an equivalence with all polynomial-time Turing machines.
-/

open OracleComp OracleSpec

namespace Signatures.Runtime.OracleCircuit

abbrev bits : Ty Empty := .list .bool

def base : Empty → Type := Empty.elim

/-- No opaque group operation or arbitrary Lean function can occur inside this instruction. -/
inductive Op : Ty Empty → Ty Empty → Type where
  | circuit (code : CircuitExecution.Code) : Op bits bits

def primitives : Primitives base Op where
  execute op input := match op with
    | .circuit code => (code.run input).value
  cost op input := match op with
    | .circuit code => (code.run input).steps

inductive Command : Ty Empty → Ty Empty → Type where
  | random : Command .unit .bool
  | hash : Command bits bits
  | sign : Command bits bits

inductive Request where
  | random
  | hash (input : List Bool)
  | sign (input : List Bool)

def spec : OracleSpec Request
  | .random => Bool
  | .hash _ => List Bool
  | .sign _ => List Bool

def semantics : Semantics base Command spec
  | _, _, .random, _ => spec.query .random
  | _, _, .hash, input => spec.query (.hash input)
  | _, _, .sign, input => spec.query (.sign input)

/-- The public key and every oracle reply are raw encodings available for arbitrary bit operations. -/
abbrev Adversary := Program Op Command [bits] bits

def Adversary.main (code : Adversary) (publicKey : List Bool) : OracleComp spec (List Bool) :=
  code.denote primitives semantics (publicKey, ())

/-- Ordinary Boolean circuits embed without an algebraicity or source-equivalence premise. -/
def ofCircuit {n : Nat} (aig : Std.Sat.AIG (Fin n)) (outputs : List (Std.Sat.AIG.Ref aig)) :
    Adversary := .ret (.op (.circuit (CircuitExecution.lower aig outputs)) (.var .here))

theorem ofCircuit_correct {n : Nat} (aig : Std.Sat.AIG (Fin n))
    (outputs : List (Std.Sat.AIG.Ref aig)) (input : Vector Bool n) :
    (ofCircuit aig outputs).main input.toList =
      pure (outputs.map fun r => Std.Sat.AIG.denote (fun i => input[i]) ⟨aig, r⟩) := by
  change pure ((CircuitExecution.lower aig outputs).run input.toList).value = _
  rw [CircuitExecution.lower_run, CircuitExecution.evaluate_correct]

/-- The local cost includes gate execution, memory scans, output reads, and program overhead. -/
theorem ofCircuit_cost {n : Nat} (aig : Std.Sat.AIG (Fin n))
    (outputs : List (Std.Sat.AIG.Ref aig)) (input : Vector Bool n)
    (H : Handler base Command spec) :
    (ofCircuit aig outputs).run primitives H (input.toList, ()) =
      pure ⟨(CircuitExecution.evaluate aig outputs input).value,
        (CircuitExecution.evaluate aig outputs input).steps + 3⟩ := by
  simp [ofCircuit, Program.run, Expr.run, Var.get, Var.depth, primitives,
    CircuitExecution.lower_run]
  omega

/-- Polynomial execution bound for the embedded circuit, without pricing it as a unit operation. -/
theorem ofCircuit_steps {n : Nat} (aig : Std.Sat.AIG (Fin n))
    (outputs : List (Std.Sat.AIG.Ref aig)) (input : Vector Bool n)
    (H : Handler base Command spec) (z : Run (List Bool))
    (hz : z ∈ support ((ofCircuit aig outputs).run primitives H (input.toList, ()))) :
    z.steps ≤ aig.decls.size * (4 * aig.decls.size + n + 10) +
      outputs.length * (aig.decls.size + 4) + 6 := by
  rw [ofCircuit_cost] at hz
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst z
  have h := CircuitExecution.evaluate_steps aig outputs input
  dsimp
  omega

end Signatures.Runtime.OracleCircuit
