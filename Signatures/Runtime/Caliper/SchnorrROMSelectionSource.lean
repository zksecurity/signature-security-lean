import Signatures.Runtime.Caliper.SchnorrROMSelection
import Signatures.Runtime.BackendSchnorrROMSelection

/-! The Caliper selector equals the original verified chronological fork-point
selection on every represented input, including missing and duplicate entries. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Selection
open Caliper BoundedSource

theorem Guard.source_original (qH : Nat) (value : Bool × Nat) :
    Guard.source qH value = Schnorr.guarded value qH := by
  simp only [Guard.source, Schnorr.guarded, Bool.and_eq_true, decide_eq_true_eq]

variable {w : Nat} {M F G : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq M] [DecidableEq G]

theorem source_original (qH : Nat) (value : Input M F G) :
    source qH value = Schnorr.selectValue value.2.1.1.1 value.2.1.1.2 value.1.1 value.1.2 value.2.1.2.2 qH := by
  simp only [source, verified, decide_eq_true_eq, sub_eq_iff_eq_add,
    Guard.source_original, ChronologicalIndex.value, Schnorr.selectValue]

theorem source_forkPoint (qH : Nat) (value : Input M F G) :
    Schnorr.asIndex qH (source qH value) =
      FiatShamir.Fork.forkPoint G F F M qH
        (Schnorr.passTrace value.2.1.1.1 value.2.1.1.2 value.1.1 value.1.2 value.2.1.2.1 value.2.1.2.2) := by
  rw [source_original]
  exact Schnorr.selectValue_forkPoint _ _ _ _ _ _ _

variable [DecidableEq F]
theorem source_selectPass (cost : PrimitiveCosts) (qH : Nat) (value : Input M F G) :
    Schnorr.asIndex qH (source qH value) =
      Schnorr.selectPass (G₂ := G) (K := M) cost qH (value.1, value.2.1) := by
  rw [source_original]
  exact (Schnorr.ListROM.NativeSelection.source_singleton (G₂ := G) (K := M) cost qH (value.1, value.2.1))

end Signatures.Runtime.CaliperBackend.SchnorrROM.Selection
