import Proofs.Runtime.Caliper.SchnorrROMReplayMatchBounds

/-! Slot comparison agrees with the original optional fork-point test. Its
rejection case includes cutoff, invalid signatures and a missing LIVE entry. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayMatch
open Caliper BoundedSource

theorem check_asIndex (qH : Nat) (slot : Fin (qH + 1)) (value : Bool × Nat) :
    Check.source (value, slot.val) = decide (Schnorr.asIndex qH value = some slot) := by
  rcases value with ⟨flag, ordinal⟩
  rcases slot with ⟨target, bound⟩
  cases flag
  · simp [Check.source, Schnorr.asIndex]
  · by_cases same : ordinal = target
    · subst ordinal
      simp [Check.source, Schnorr.asIndex, bound]
    · simp [Check.source, Schnorr.asIndex, same]

variable {w : Nat} {M F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
    [DecidableEq M] [DecidableEq G] (config : Signing.Enumerated.Configuration w M F G)

theorem source_original (cost : PrimitiveCosts) (qH : Nat) (value : Frame config) (slot : Fin (qH + 1))
    (target : value.2.1.1.val = slot.val) :
    (source config qH value).1.val = decide ((Terminal.observed config value.1).1.bind (fun returned =>
      Schnorr.selectPass (G₂ := G) (K := M) cost qH (returned, value.1.2.val.1)) = some slot) := by
  change Check.source (PassSelection.source config qH value.1, value.2.1.1.val) = _
  rw [target, check_asIndex, PassSelection.source_original config cost qH value.1]

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayMatch
