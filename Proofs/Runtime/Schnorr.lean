import Proofs.Runtime.Machine
import Examples.Schnorr.SigmaProtocol

/-! Concrete arithmetic for Schnorr's signing simulation and two-transcript extraction.
The complete cache/replay solver and its certificate are in SchnorrReduction. -/

open OracleComp

namespace Signatures.Runtime.Schnorr

/-- Given `z, c, g, pk`, construct the simulated commitment `z*g - c*pk`. -/
def simulatedCommit : Expr CryptoOp [scalar, scalar, point₁, point₁] point₁ :=
  .op .sub₁ (.pair
    (.op .scale₁ (.pair (.var .here) (.var (.there (.there .here)))))
    (.op .scale₁ (.pair (.var (.there .here)) (.var (.there (.there (.there .here)))))))

/-- Given `z, z', c, c'`, recover the candidate `(z-z')/(c-c')`.
The caller must reject equal challenges before claiming special soundness. -/
def extract : Expr CryptoOp [scalar, scalar, scalar, scalar] scalar :=
  .op .div (.pair
    (.op .sub (.pair (.var .here) (.var (.there .here))))
    (.op .sub (.pair (.var (.there (.there .here))) (.var (.there (.there (.there .here)))))))

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

theorem simulatedCommit_run (cost : PrimitiveCosts) (z c : F) (g pk : G) :
    simulatedCommit.run (arithmetic F G G Unit Unit cost) (z, c, g, pk, ()) =
      ⟨z • g - c • pk, 2 * cost.scalar₁ + cost.group + 16⟩ := by
  simp [simulatedCommit, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price]
  omega

theorem extract_run (cost : PrimitiveCosts) (z z' c c' : F) :
    extract.run (arithmetic F G G Unit Unit cost) (z, z', c, c', ()) =
      ⟨(z - z') / (c - c'), 2 * cost.field + cost.division + 16⟩ := by
  simp [extract, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price]
  omega

/-- The implemented candidate is a discrete logarithm only with distinct challenges and
two accepting transcripts for the same commitment. Zero secret keys are allowed. -/
theorem extract_sound (cost : PrimitiveCosts) (g pk R : G) (z z' c c' : F)
    (hne : c ≠ c') (h : z • g = R + c • pk) (h' : z' • g = R + c' • pk) :
    (extract.run (arithmetic F G G Unit Unit cost) (z, z', c, c', ())).value • g = pk := by
  have hdiff : (z - z') • g = (c - c') • pk := by
    rw [sub_smul, sub_smul, h, h']
    abel
  rw [extract_run]
  change ((z - z') / (c - c')) • g = pk
  rw [div_eq_mul_inv, mul_comm, mul_smul, hdiff,
    inv_smul_smul₀ (sub_ne_zero.mpr hne)]

end Signatures.Runtime.Schnorr
