import Proofs.Runtime.HeapProbability
import Proofs.Runtime.HeapCodeSize

/-! DLog hardness for the bit-heap machine. Challenges arrive as encoded
inputs, and returned heap roots are observed as scalar encodings. The success
test is mathematical; the solver's online operations are exactly Package.run. -/

namespace Signatures.Runtime.HeapMachine

open OracleComp WeierstrassCurve
open scoped ENNReal

variable {p : Nat} [Fact p.Prime] {W : Affine (ZMod p)}

noncomputable def scalarLaw (r w : Nat) (pack : Package) (pk : W.Point) : PMF (ZMod r × Bool) :=
  (simulateQ fairBits (pack.run [.word (CryptoCircuit.pointBits (w := w) pk)])).map
      (fun out => (scalarValue r out.1.value, out.2))

/-- Bound stored code/data separately from online work on every random-bit path. -/
def dlogWithin (w : Nat) (H : AddSubgroup W.Point) (codeBudget budget : Nat) (pack : Package) : Prop :=
  pack.cells ≤ codeBudget ∧
  ∀ pk : H, ∀ out ∈ support (pack.run [.word (CryptoCircuit.pointBits (w := w) (pk : W.Point))]),
      out.1.steps ≤ budget

noncomputable def dlogAdvantage {r : Nat} [Fact r.Prime] {H : AddSubgroup W.Point}
    [Module (ZMod r) H] (w : Nat) (g : H) (pack : Package) : ℝ≥0∞ :=
  ((PMF.uniformOfFintype (ZMod r)).bind (fun x =>
    (scalarLaw r w pack ((x • g : H) : W.Point)).map (fun out => decide (out.1 = x)))) true

end Signatures.Runtime.HeapMachine
