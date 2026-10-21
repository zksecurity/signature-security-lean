import Signatures.Runtime.Caliper.SchnorrROMReplayForkMemory

/-! The first Boolean gate is exactly the original optional fork-point gate.
A true flag always has an in-allowance ordinal; it cannot hide `asIndex = none`. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type}

theorem guarded_range (qH : Nat) (value : Bool × Nat) :
    (Selection.Guard.source qH value).1 = true → (Selection.Guard.source qH value).2 < qH + 1 := by
  unfold Selection.Guard.source
  split
  · intro _
    have accepted := ‹(value.1 && decide (value.2 < qH + 1)) = true›
    simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
    exact accepted.2
  · simp

theorem indexed_flag (qH : Nat) (value : Bool × Nat) (range : value.1 = true → value.2 < qH + 1) :
    (Schnorr.asIndex qH value).isSome = value.1 := by
  rcases value with ⟨flag, ordinal⟩
  cases flag
  · simp [Schnorr.asIndex]
  · have bounded := range rfl
    simp [Schnorr.asIndex, bounded]

section Runtime
variable [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

omit [Zero F] in
theorem selection_range (qH : Nat) (value : Selection.Input M F G) :
    (Selection.source qH value).1 = true → (Selection.source qH value).2 < qH + 1 := by
  unfold Selection.source
  split
  · exact guarded_range qH _
  · simp
omit [Zero F] in
theorem pass_range (qH : Nat) (value : Terminal.Output config) :
    (PassSelection.source config qH value).1 = true → (PassSelection.source config qH value).2 < qH + 1 := by
  rcases value with ⟨cutoff | returned, store⟩
  · simp [PassSelection.source]
  · exact selection_range qH _
end Runtime

section Original
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (ops : Handler.Operations config) (qH : Nat) (indexFits : qH + 1 < 2 ^ w)

theorem first_gate_original (cost : PrimitiveCosts) (first : Terminal.Output config) :
    (ReplayFirst.choose config (ReplayFirst.selectedValue config ops qH indexFits first)).isRight =
      ((Terminal.observed config first).1.bind (fun returned =>
        Schnorr.selectPass (G₂ := G) (K := M) cost qH (returned, first.2.val.1))).isSome := by
  rw [← PassSelection.source_original config cost qH first,
    indexed_flag qH (PassSelection.source config qH first) (pass_range config qH first)]
  cases selected : (PassSelection.source config qH first).1 <;>
    simp [ReplayFirst.choose, ReplayFirst.selectedValue, selected]
theorem second_exit_original (cost : PrimitiveCosts) (value : ReplayMatch.Frame config)
    (slot : Fin (qH + 1)) (target : value.2.1.1.val = slot.val) :
    finishSource config (ReplayMatch.source config qH value) =
      if (Terminal.observed config value.1).1.bind (fun returned =>
          Schnorr.selectPass (G₂ := G) (K := M) cost qH (returned, value.1.2.val.1)) = some slot then
        .inr (value.2.2, value.1) else .inl () := by
  unfold finishSource
  rw [ReplayMatch.source_original config cost qH value slot target]
  simp only [decide_eq_true_eq]
  rfl
end Original

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
