import Proofs.Runtime.Caliper.Interactive

/-! Executed tag dispatch and bounded interactive loops. The compiled control
selects branches using stored word tags, and can suspend on oracle calls at any
iteration. Source refinement carries the exact executed state/profile throughout.
-/

namespace Signatures.Runtime.CaliperBackend.Interactive

open Caliper OracleComp OracleSpec

variable {w : Nat} {I A B D : Type} {spec : OracleSpec I}

/-- Prepending executed local work preserves the source query tree. The actual
prefix profile and trace are combined with the continuation's execution. -/
theorem prepend_exec (port : Port w spec) (cost : WordIO.Costs) (tape : RandomTape w)
    {prefixCode : Stmt w} {body : Code w} {before middle : State w}
    {time : Nat} {net peak : Int} {output : Representation w B} {source : OracleComp spec B}
    (prefixExec : Caliper.Exec cost.machine tape prefixCode before middle time net peak)
    (bodyRefines : Synchronizes (Represents output cost tape (body.lower port) middle) source
      (body.execute port cost tape middle)) :
    Synchronizes (Represents output cost tape ((Code.seq (.compute prefixCode) body).lower port) before)
      source ((Code.seq (.compute prefixCode) body).execute port cost tape before) := by
  rw [Code.execute, execute_of_exec port cost tape prefixExec]
  simp only [pure_bind]
  simpa using bodyRefines.map id (fun result => join ⟨middle, time, net, peak, [], []⟩ <$> result) (by
    intro value result related
    obtain ⟨finished, rfl, holds, remaining, execution⟩ := related
    exact ⟨join ⟨middle, time, net, peak, [], []⟩ finished, rfl, holds, remaining,
      .seq (.compute prefixExec) execution⟩)

def dispatch (left right : Code w) (leftWords rightWords : Nat) : Code w :=
  .seq (.compute (.memLoad 1 0 0))
    (.branch 1 (.seq (.compute (selectSlice 1 rightWords)) right)
      (.seq (.compute (selectSlice 1 leftWords)) left))

theorem payload_exec (cost : WordIO.Costs) (tape : RandomTape w) (port : Port w spec)
    {input : Representation w A} {output : Representation w B} {source : A → OracleComp spec B}
    {body : Code w} (bodyRefines : Refines port cost input output source body)
    (value : A) (tag : Word w) (padding : List (Word w)) (before : State w)
    (zero : before.regs 0 = 0)
    (contents : (before.bufs 0).toList = tag :: (input.encoding.encode value ++ padding))
    (wellFormed : before.WellFormed) (capacities : ∀ buffer, before.caps buffer < 2 ^ w) :
    Synchronizes (Represents output cost tape ((Code.seq (.compute (selectSlice 1 input.encoding.words)) body).lower port) before)
      (source value) ((Code.seq (.compute (selectSlice 1 input.encoding.words)) body).execute port cost tape before) := by
  have length := congrArg List.length contents
  have span : 1 + input.encoding.words ≤ (before.bufs 0).size := by
    simp only [Array.length_toList, List.length_cons, List.length_append, input.encoding.encode_length] at length
    omega
  obtain ⟨middle, time, net, peak, execution, payload, offset, caps⟩ :=
    selectSlice_exec cost.machine tape 1 input.encoding.words before span capacities wellFormed
  apply prepend_exec port cost tape execution
  apply bodyRefines tape value middle
  refine ⟨offset.trans zero, ?_, execution.wellFormed_preserved wellFormed, caps⟩
  rw [payload, contents, ← input.encoding.encode_length value]
  simp

theorem Refines.dispatch {port : Port w spec} {cost : WordIO.Costs}
    (left : Representation w A) (right : Representation w B) (output : Representation w D)
    {f : A → OracleComp spec D} {g : B → OracleComp spec D} {leftBody rightBody : Code w}
    (leftRefines : Refines port cost left output f leftBody)
    (rightRefines : Refines port cost right output g rightBody)
    (hw : 0 < w) (fits : 1 + max left.encoding.words right.encoding.words < 2 ^ w) :
    Refines port cost (left.sum right hw fits) output (Sum.elim f g)
      (dispatch leftBody rightBody left.encoding.words right.encoding.words) := by
  intro tape value before represented
  cases value with
  | inl value =>
    have contents : (before.bufs 0).toList = (0 : Word w) :: (left.encoding.encode value ++
        List.replicate (max left.encoding.words right.encoding.words - left.encoding.words) 0) := represented.2.1
    have loaded := Dispatch.load_tag cost.machine tape 0 _ before represented.1 contents
    apply prepend_exec port cost tape loaded
    have payload := payload_exec cost tape port leftRefines value 0 _ (before.setReg 1 0)
      (by simpa using represented.1) contents (loaded.wellFormed_preserved represented.2.2.1) represented.2.2.2
    rw [Code.execute, ite_eq_left (show (before.setReg 1 0).regs 1 = 0 by simp)]
    simpa only [id_map, Sum.elim_inl, Sum.elim_inr] using payload.map
      (result := Represents output cost tape
        ((Code.branch 1 (.seq (.compute (selectSlice 1 right.encoding.words)) rightBody)
          (.seq (.compute (selectSlice 1 left.encoding.words)) leftBody)).lower port) (before.setReg 1 0)) id
      (fun result => (fun finished => { finished with time := cost.machine.branch + finished.time }) <$> result) (by
        intro answer result related
        obtain ⟨finished, rfl, holds, remaining, execution⟩ := related
        exact ⟨{ finished with time := cost.machine.branch + finished.time }, rfl, holds, remaining,
          .branch_no (by simp) execution⟩)
  | inr value =>
    have contents : (before.bufs 0).toList = (1 : Word w) :: (right.encoding.encode value ++
        List.replicate (max left.encoding.words right.encoding.words - right.encoding.words) 0) := represented.2.1
    have loaded := Dispatch.load_tag cost.machine tape 1 _ before represented.1 contents
    apply prepend_exec port cost tape loaded
    have payload := payload_exec cost tape port rightRefines value 1 _ (before.setReg 1 1)
      (by simpa using represented.1) contents (loaded.wellFormed_preserved represented.2.2.1) represented.2.2.2
    have nonzero : (before.setReg 1 1).regs 1 ≠ 0 := by simp [hw.ne']
    rw [Code.execute, ite_eq_right nonzero]
    simpa only [id_map, Sum.elim_inl, Sum.elim_inr] using payload.map
      (result := Represents output cost tape
        ((Code.branch 1 (.seq (.compute (selectSlice 1 right.encoding.words)) rightBody)
          (.seq (.compute (selectSlice 1 left.encoding.words)) leftBody)).lower port) (before.setReg 1 1)) id
      (fun result => (fun finished => { finished with time := cost.machine.branch + finished.time }) <$> result) (by
        intro answer result related
        obtain ⟨finished, rfl, holds, remaining, execution⟩ := related
        exact ⟨{ finished with time := cost.machine.branch + finished.time }, rfl, holds, remaining,
          .branch_yes nonzero execution⟩)

def loop (body stop : Code w) (resultWords stateWords : Nat) : Nat → Code w
  | 0 => stop
  | fuel + 1 => .seq body (dispatch (.compute .skip) (loop body stop resultWords stateWords fuel) resultWords stateWords)

theorem Refines.loop {port : Port w spec} {cost : WordIO.Costs}
    (state : Representation w A) (result : Representation w B) (hw : 0 < w)
    (fits : 1 + max result.encoding.words state.encoding.words < 2 ^ w)
    {f : A → OracleComp spec (B ⊕ A)} {g : A → OracleComp spec B} {body stop : Code w}
    (bodyRefines : Refines port cost state (result.sum state hw fits) f body)
    (stopRefines : Refines port cost state result g stop) (fuel : Nat) :
    Refines port cost state result (BackendProgram.loopDenote f g fuel)
      (Interactive.loop body stop result.encoding.words state.encoding.words fuel) := by
  induction fuel with
  | zero => exact stopRefines
  | succ fuel ih =>
    convert bodyRefines.seq (Refines.dispatch result state result
      (Refines.compute port cost (Realizer.identity hw result)) ih hw fits) using 1
    · funext value
      rw [BackendProgram.loopDenote]
      congr 1
      funext answer
      cases answer <;> rfl
    · rfl

end Signatures.Runtime.CaliperBackend.Interactive
