import Signatures.Runtime.Caliper.Counter
import Signatures.Runtime.Caliper.InteractiveControlBounds

/-! Input-counted interactive iteration. The input frame stores a payload then a
counter; each positive iteration decrements the stored word before saving it
across the callee. The static bound controls code generation, while actual tests
of the stored counter control execution and early termination.
-/

namespace Signatures.Runtime.CaliperBackend.Interactive

open Caliper OracleComp OracleSpec

variable {w : Nat} {I A : Type} {spec : OracleSpec I}

namespace Counted

def frame (state : Representation w A) (fuel : Nat) (hw : 16 < 2 ^ w)
    (counterFits : fuel + 1 ≤ 2 ^ w) (storageFits : state.encoding.words + 1 < 2 ^ w) :
    Representation w (A × Fin (fuel + 1)) :=
  state.prod (Representation.fin w (fuel + 1) (width_pos hw) counterFits) storageFits

def code (body : Code w) (buffer stateWords : Nat) : Nat → Code w
  | 0 => .compute (selectSlice 0 stateWords)
  | fuel + 1 => .seq (.compute (Counter.load stateWords))
      (.branch 2
        (.seq (.compute Counter.decrement)
          (.seq (retain body buffer stateWords stateWords 1) (code body buffer stateWords fuel)))
        (.compute (selectSlice 0 stateWords)))

private theorem branch_no_at (port : Port w spec) (cost : WordIO.Costs) (tape : RandomTape w)
    (condition : Reg) (yes no : Code w) (before : State w) (zero : before.regs condition = 0)
    (output : Representation w A) (source : OracleComp spec A)
    (related : Synchronizes (Represents output cost tape (no.lower port) before) source (no.execute port cost tape before)) :
    Synchronizes (Represents output cost tape ((Code.branch condition yes no).lower port) before)
      source ((Code.branch condition yes no).execute port cost tape before) := by
  rw [Code.execute, ite_eq_left zero]
  simpa only [id_map] using related.map
    (result := Represents output cost tape ((Code.branch condition yes no).lower port) before) id
    (fun result => (fun finished => { finished with time := cost.machine.branch + finished.time }) <$> result) (by
      intro value result realization
      obtain ⟨finished, rfl, holds, remaining, execution⟩ := realization
      exact ⟨{ finished with time := cost.machine.branch + finished.time }, rfl, holds, remaining,
        .branch_no zero execution⟩)

private theorem branch_yes_at (port : Port w spec) (cost : WordIO.Costs) (tape : RandomTape w)
    (condition : Reg) (yes no : Code w) (before : State w) (nonzero : before.regs condition ≠ 0)
    (output : Representation w A) (source : OracleComp spec A)
    (related : Synchronizes (Represents output cost tape (yes.lower port) before) source (yes.execute port cost tape before)) :
    Synchronizes (Represents output cost tape ((Code.branch condition yes no).lower port) before)
      source ((Code.branch condition yes no).execute port cost tape before) := by
  rw [Code.execute, ite_eq_right nonzero]
  simpa only [id_map] using related.map
    (result := Represents output cost tape ((Code.branch condition yes no).lower port) before) id
    (fun result => (fun finished => { finished with time := cost.machine.branch + finished.time }) <$> result) (by
      intro value result realization
      obtain ⟨finished, rfl, holds, remaining, execution⟩ := realization
      exact ⟨{ finished with time := cost.machine.branch + finished.time }, rfl, holds, remaining,
        .branch_yes nonzero execution⟩)

theorem refines {port : Port w spec} {cost : WordIO.Costs} (state : Representation w A)
    {source : A → OracleComp spec A} {body : Code w}
    (bodyRefines : Refines port cost state state source body) (allocation : 1 ≤ cost.machine.allocPerWord)
    (hw : 16 < 2 ^ w) (storageFits : state.encoding.words + 1 < 2 ^ w)
    (fuel : Nat) (counterFits : fuel + 1 ≤ 2 ^ w) :
    Refines port cost (frame state fuel hw counterFits storageFits) state
      (fun value => repeatDenote source value.2.val value.1)
      (code body (savedBuffer port body) state.encoding.words fuel) := by
  induction fuel with
  | zero =>
    intro tape value before represented
    have zero : value.2.val = 0 := by have := value.2.isLt; omega
    dsimp only
    rw [zero]
    exact Refines.compute port cost
      (firstRealizer cost.machine allocation state (Representation.fin w 1 (width_pos hw) counterFits) hw storageFits)
      tape value before represented
  | succ fuel ih =>
    intro tape value before represented
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
    apply prepend_exec port cost tape loading
    cases count with
    | zero =>
      apply branch_no_at port cost tape 2 _ _ loaded (by simp [loaded]) state
      exact Refines.compute port cost
        (firstRealizer cost.machine allocation state
          (Representation.fin w (fuel + 1 + 1) (width_pos hw) counterFits) hw storageFits)
        tape (value, ⟨0, valid⟩) loaded ready
    | succ count =>
      have wordBound : count + 1 < 2 ^ w := valid.trans_le counterFits
      have nonzero : loaded.regs 2 ≠ 0 := by
        intro equal
        have numeric := congrArg BitVec.toNat equal
        simp [loaded, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordBound] at numeric
      apply branch_yes_at port cost tape 2 _ _ loaded nonzero state
      obtain ⟨decreased, decreasing, bytes, zero, capacities⟩ :=
        Counter.decrement_exec cost.machine tape payload count loaded (by simpa [loaded] using contents)
          (by simp [loaded]) ready.2.2.1
      apply prepend_exec port cost tape decreasing
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
      have rest := retained.seq (ih smallerFits)
      simpa only [bind_map_left, repeatDenote, counter, Representation.fin, Encoding.fin, Encoding.checked] using
        rest tape (value, ⟨count, by omega⟩) decreased next

end Counted
end Signatures.Runtime.CaliperBackend.Interactive
