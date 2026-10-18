import Signatures.Runtime.Caliper.Counted
import Signatures.Runtime.Caliper.InteractiveAcceptance
import Signatures.Runtime.Caliper.InteractiveDescription

/-! Runtime, stored-code and word-width bounds for counted interactive iteration.
The actual counter test, decrement, preservation across calls and final projection
are all included. Code generation unrolls the supplied maximum count.
-/

namespace Signatures.Runtime.CaliperBackend.Interactive.Counted

open Caliper OracleComp OracleSpec

variable {w : Nat} {I A : Type} {spec : OracleSpec I}

def overhead (cost : WordIO.Costs) (buffer stateWords bodyBudget : Nat) : Nat :=
  (Counter.load (w := w) stateWords).staticTime cost.machine + cost.machine.branch +
    (Counter.decrement (w := w)).staticTime cost.machine +
    ((Retain.prepare (w := w) buffer stateWords 1).staticTime cost.machine +
      (bodyBudget + (Retain.finish (w := w) buffer stateWords 1).staticTime cost.machine))

def budget (cost : WordIO.Costs) (buffer stateWords bodyBudget fuel : Nat) : Nat :=
  (selectSlice (w := w) 0 stateWords).staticTime cost.machine + fuel * overhead (w := w) cost buffer stateWords bodyBudget

theorem timeBound {port : Port w spec} {cost : WordIO.Costs} (state : Representation w A)
    {source : A → OracleComp spec A} {body : Code w} {bodyBudget : Nat}
    (bodyRefines : Refines port cost state state source body) (bodyBound : TimeBound port cost state body bodyBudget)
    (allocation : 1 ≤ cost.machine.allocPerWord) (hw : 16 < 2 ^ w)
    (storageFits : state.encoding.words + 1 < 2 ^ w) (fuel : Nat) (counterFits : fuel + 1 ≤ 2 ^ w) :
    TimeBound port cost (frame state fuel hw counterFits storageFits)
      (code body (savedBuffer port body) state.encoding.words fuel)
      (budget (w := w) cost (savedBuffer port body) state.encoding.words bodyBudget fuel) := by
  induction fuel with
  | zero =>
    simpa [code, budget] using TimeBound.compute_loopFree (port := port) (cost := cost)
      (frame state 0 hw counterFits storageFits) (selectSlice 0 state.encoding.words) (selectSlice_straight _ _).loopFree
  | succ fuel ih =>
    intro tape value before represented finished reached
    rcases value with ⟨value, ⟨count, valid⟩⟩
    let payload := (state.encoding.encode value).toArray
    have payloadSize : payload.size = state.encoding.words := by simp [payload, state.encoding.encode_length]
    have contents : before.bufs 0 = payload.push (BitVec.ofNat w count) := by
      apply Array.toList_inj.mp
      simpa [payload, frame, Representation.prod, Representation.fin, Encoding.prod, Encoding.fin, Encoding.checked] using represented.2.1
    have loading := Counter.load_exec cost.machine tape payload (BitVec.ofNat w count) before contents
      (by rw [payloadSize]; exact state.fits)
    rw [payloadSize] at loading
    let loaded := (before.setReg 1 (BitVec.ofNat w state.encoding.words)).setReg 2 (BitVec.ofNat w count)
    have ready : (frame state (fuel + 1) hw counterFits storageFits).Holds (value, ⟨count, valid⟩) loaded :=
      ⟨by simpa [loaded] using represented.1, by simpa [loaded] using represented.2.1,
        loading.wellFormed_preserved represented.2.2.1, represented.2.2.2⟩
    let projection := (selectSlice (w := w) 0 state.encoding.words).staticTime cost.machine
    let retaining := (Retain.prepare (w := w) (savedBuffer port body) state.encoding.words 1).staticTime cost.machine +
      (bodyBudget + (Retain.finish (w := w) (savedBuffer port body) state.encoding.words 1).staticTime cost.machine)
    let decrementing := (Counter.decrement (w := w)).staticTime cost.machine
    let restBudget := budget (w := w) cost (savedBuffer port body) state.encoding.words bodyBudget fuel
    have bound : finished.time ≤ (cost.machine.imm + cost.machine.memLoad) +
        (cost.machine.branch + max projection (decrementing + (retaining + restBudget))) := by
      apply time_prepend_at tape loading _ finished reached
      apply time_branch_at
      cases count with
      | zero =>
        rw [ite_eq_left (show loaded.regs 2 = 0 by simp [loaded])]
        intro result resultReached
        exact (TimeBound.compute_loopFree (port := port) (cost := cost)
          (frame state (fuel + 1) hw counterFits storageFits) (selectSlice 0 state.encoding.words)
          (selectSlice_straight _ _).loopFree tape (value, ⟨0, valid⟩) loaded ready result resultReached).trans (le_max_left _ _)
      | succ count =>
        have wordBound : count + 1 < 2 ^ w := valid.trans_le counterFits
        have nonzero : loaded.regs 2 ≠ 0 := by
          intro equal
          have numeric := congrArg BitVec.toNat equal
          simp [loaded, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordBound] at numeric
        rw [ite_eq_right nonzero]
        intro result resultReached
        apply le_trans _ (le_max_right _ _)
        obtain ⟨decreased, decreasing, bytes, zero, capacities⟩ :=
          Counter.decrement_exec cost.machine tape payload count loaded (by simpa [loaded] using contents)
            (by simp [loaded]) ready.2.2.1
        apply time_prepend_at tape decreasing _ result resultReached
        have smallerFits : fuel + 1 ≤ 2 ^ w := by omega
        let counter := Representation.fin w (fuel + 1) (width_pos hw) smallerFits
        have next : (frame state fuel hw smallerFits storageFits).Holds (value, ⟨count, by omega⟩) decreased := by
          refine ⟨zero.trans ready.1, ?_, decreasing.wellFormed_preserved ready.2.2.1, ?_⟩
          · change (decreased.bufs 0).toList = state.encoding.encode value ++ [BitVec.ofNat w count]
            rw [bytes]
            simp [payload]
          · intro buffer
            rw [capacities]
            exact ready.2.2.2 buffer
        have retained := bodyRefines.retain allocation counter hw storageFits storageFits
        have retainedBound := bodyBound.retain bodyRefines allocation counter hw storageFits
        have rest := retainedBound.seq retained (ih smallerFits)
        simpa only [counter, Representation.fin, Encoding.fin, Encoding.checked] using
          rest tape (value, ⟨count, by omega⟩) decreased next
    simp only [budget, overhead, Counter.load, Counter.decrement, Stmt.staticTime, Nat.succ_mul,
      projection, decrementing, retaining, restBudget] at *
    omega

theorem descriptionFits (port : Port w spec) (body : Code w) (buffer stateWords fuel : Nat)
    (hw : 16 < 2 ^ w) (bodyFits : (body.lower port).DescriptionFits)
    (name : buffer < 2 ^ w) (storage : stateWords + 1 < 2 ^ w) :
    ((code body buffer stateWords fuel).lower port).DescriptionFits := by
  have stateFits : stateWords < 2 ^ w := by omega
  have one : 1 < 2 ^ w := Nat.one_lt_two_pow (width_pos hw).ne'
  induction fuel with
  | zero => exact .compute (selectSlice_descriptionFits _ _ hw stateFits)
  | succ fuel ih =>
    apply WordIO.Code.DescriptionFits.seq hw (.compute (Counter.load_descriptionFits stateWords hw))
    apply WordIO.Code.DescriptionFits.branch (condition := 2) hw (lt_trans (by decide : 2 < 16) hw)
    · exact WordIO.Code.DescriptionFits.seq hw (.compute (Counter.decrement_descriptionFits hw))
        (WordIO.Code.DescriptionFits.seq hw
          (retain_descriptionFits port body buffer stateWords stateWords 1 hw bodyFits name stateFits one storage) ih)
    · exact .compute (selectSlice_descriptionFits _ _ hw stateFits)

theorem descriptionWords_le (port : Port w spec) (body : Code w) (buffer stateWords fuel : Nat) :
    ((code body buffer stateWords fuel).lower port).descriptionWords ≤
      26 * stateWords + 15 + fuel * ((body.lower port).descriptionWords + 78 * stateWords + 126) := by
  induction fuel with
  | zero => simp [code, Code.lower, WordIO.Code.descriptionWords_compute, selectSlice_descriptionWords]
  | succ fuel ih =>
    have retained := retain_descriptionWords_le port body buffer stateWords stateWords 1
    have loadWords : descriptionWords (Counter.load (w := w) stateWords) = 8 := rfl
    have decrementWords : descriptionWords (Counter.decrement (w := w)) = 16 := rfl
    simp only [code, Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_branch,
      WordIO.Code.descriptionWords_compute, loadWords, decrementWords, selectSlice_descriptionWords, Nat.succ_mul] at *
    omega

theorem budget_unit_le (buffer stateWords bodyBudget fuel : Nat) :
    budget (w := w) .unit buffer stateWords bodyBudget fuel ≤ 8 * stateWords + fuel * (bodyBudget + 16 * stateWords + 19) := by
  have retained := retain_time_unit_le (w := w) buffer stateWords stateWords 1 bodyBudget
  simp only [CostModel.unit] at retained
  have step : overhead (w := w) .unit buffer stateWords bodyBudget ≤ bodyBudget + 16 * stateWords + 19 := by
    simp only [overhead, Counter.load, Counter.decrement, Stmt.staticTime, WordIO.Costs.unit, CostModel.unit]
    omega
  have multiplied := Nat.mul_le_mul_left fuel step
  simp only [budget, selectSlice_staticTime, sliceWordTime, WordIO.Costs.unit, CostModel.unit] at *
  omega

end Signatures.Runtime.CaliperBackend.Interactive.Counted
