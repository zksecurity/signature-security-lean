import Proofs.Runtime.Caliper.Within
import Proofs.Runtime.PolynomialNegligible

/-! Nonuniform families of actual Caliper programs. Word widths, ports and
layouts are fixed before the algorithm family. One polynomial bounds each of
word width, stored code, total memory and runtime across all parameters. The
code at each parameter works for every represented input and local tape. This
is a word-machine resource class, not a CPU simulation or a uniform compiler. -/
namespace Signatures.Runtime.CaliperBackend.Interactive
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat → Nat} {A B : Nat → Type} {I : Type} {spec : OracleSpec I}
    (port : ∀ n, Port (w n) spec) (input : ∀ n, Layout (w n) (A n))
    (output : ∀ n, Layout (w n) (B n))

def NonuniformWithin (algorithm : ∀ n, (input n).Value → OracleComp spec (B n)) : Prop :=
  PolynomiallyBounded w ∧
  ∃ words memory time : Nat → Nat,
    PolynomiallyBounded words ∧ PolynomiallyBounded memory ∧ PolynomiallyBounded time ∧
    ∀ n, Within (port n) (input n) (output n) (words n) (memory n) (time n) (algorithm n)

theorem NonuniformWithin.of_pointwise
    (algorithm : ∀ n, (input n).Value → OracleComp spec (B n)) (words memory time : Nat → Nat)
    (width : PolynomiallyBounded w) (stored : PolynomiallyBounded words)
    (space : PolynomiallyBounded memory) (elapsed : PolynomiallyBounded time)
    (implemented : ∀ n, Within (port n) (input n) (output n) (words n) (memory n) (time n) (algorithm n)) :
    NonuniformWithin port input output algorithm :=
  ⟨width, words, memory, time, stored, space, elapsed, implemented⟩

end Signatures.Runtime.CaliperBackend.Interactive
