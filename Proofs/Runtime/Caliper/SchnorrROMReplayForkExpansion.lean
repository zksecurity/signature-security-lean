import Proofs.Runtime.Caliper.SchnorrROMReplayInitializedBounds

/-! Expand the executed controller into the original optional-index branches.
These equations preserve the draw order and both complete terminal results. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type}

theorem asIndex_some (qH : Nat) (value : Bool × Nat) (slot : Fin (qH + 1))
    (selected : Schnorr.asIndex qH value = some slot) : value.1 = true ∧ value.2 = slot.val := by
  unfold Schnorr.asIndex at selected
  split at selected
  · rename_i valid
    exact ⟨valid.1, congrArg Fin.val (Option.some.inj selected)⟩
  · simp at selected

variable [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G] [DecidableEq F]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Pass.Caller config A)
    (ops : Handler.Operations config) (qH : Nat) (indexFits : qH + 1 < 2 ^ w)

def counterOfIndex (slot : Fin (qH + 1)) : config.handler.sampler.tape.counter.Value :=
  ⟨slot.val, Nat.lt_trans slot.isLt indexFits⟩

theorem afterSource_expand (fuel : Nat) (value : ReplayChallenge.Input config) :
    afterSource config caller ops qH fuel value =
      (PrivateSampler.Enumerated.Direct.source config.sampler >>= fun replacement =>
        if (Schnorr.RawTape.values (.inr ()) value.2.2.val.2.1)[value.1.val]? = some replacement.val then
          pure (.inl ()) else secondSource config caller ops qH fuel ((value.1, replacement), value.2)) := by
  unfold afterSource guardChoiceSource ReplayChallenge.Checked.source ReplayChallenge.source
  simp only [bind_map_left]
  erw [bind_map_left, bind_map_left]
  apply bind_congr
  intro replacement
  unfold chooseGuard
  erw [ReplayChallenge.Guard.source_original]
  simp only [decide_eq_true_eq]
  split <;> rfl

theorem source_expand (fuel : Nat)
    (value : {value : Pass.Initialization.Input config // Pass.Replay.ready config fuel value}) :
    source config caller ops qH indexFits fuel value =
      (Pass.source config caller ops fuel value.val >>= fun first =>
        match Schnorr.asIndex qH (PassSelection.source config qH first) with
        | none => pure (.inl ())
        | some slot => afterSource config caller ops qH fuel
            (counterOfIndex config qH indexFits slot, first)) := by
  unfold source ReplayFirst.choiceSource ReplayFirst.source
  simp only [bind_map_left]
  apply bind_congr
  intro first
  by_cases accepted : (PassSelection.source config qH first).1 = true
  · have bounded := pass_range config qH first accepted
    rw [Schnorr.asIndex, dite_eq_left ⟨accepted, bounded⟩]
    simp only [ReplayFirst.choose, ReplayFirst.selectedValue, accepted, ↓reduceIte, branchSource, Sum.elim_inr]
    rfl
  · rw [Schnorr.asIndex, dite_eq_right (by simp [accepted])]
    simp only [ReplayFirst.choose, ReplayFirst.selectedValue, accepted, Bool.false_eq_true, ↓reduceIte, branchSource, Sum.elim_inl]

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
