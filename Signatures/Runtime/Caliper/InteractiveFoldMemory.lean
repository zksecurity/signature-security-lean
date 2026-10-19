import Signatures.Runtime.Caliper.InteractiveFoldBounds
import Signatures.Runtime.Caliper.InteractiveNames
import Signatures.Runtime.Caliper.InteractiveAcceptance

/-! Stored-code, name and whole-memory bounds for the effectful fold. Every
unrolled body and early-return branch is counted, together with initial caller
capacity and all intermediate states of the same execution. -/
namespace Signatures.Runtime.CaliperBackend.InteractiveFold
open Caliper OracleComp OracleSpec
variable {w : Nat} {I : Type} {spec : OracleSpec I}

def codeBudget (entry state capacity body : Nat) : Nat :=
  26 * state + 15 + capacity * (body + 169 * width entry state capacity + 130)

variable (port : Interactive.Port w spec) (body : Interactive.Code w)

theorem continuation_words (following : Interactive.Code w) (entry state capacity : Nat) :
    ((continuation body following (Interactive.savedBuffer port body) entry state capacity).lower port).descriptionWords ≤
      (body.lower port).descriptionWords + (following.lower port).descriptionWords + 26 * (entry + state) + 26 * state +
        39 * (1 + capacity * entry) + 26 * (state + (1 + capacity * entry)) + 58 := by
  have retained := Interactive.retain_descriptionWords_le port body (Interactive.savedBuffer port body) (entry + state) state (1 + capacity * entry)
  have reordered := Reorder.descriptionWords_le (w := w) state (1 + capacity * entry) 0
  simp only [continuation, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega

theorem code_bound (entry state capacity : Nat) {bodyWords : Nat} (bodyBound : (body.lower port).descriptionWords ≤ bodyWords) :
    ((code body (Interactive.savedBuffer port body) entry state capacity).lower port).descriptionWords ≤ codeBudget entry state capacity bodyWords := by
  induction capacity with
  | zero => simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_compute, selectSlice_descriptionWords, codeBudget, Nat.zero_mul, Nat.add_zero]; omega
  | succ capacity ih =>
    have continued := continuation_words port body (code body (Interactive.savedBuffer port body) entry state capacity) entry state capacity
    have prepared := ListFold.prepare_descriptionWords_le (w := w) entry state 0 capacity
    have monotone : width entry state capacity ≤ width entry state (capacity + 1) := by dsimp [width]; nlinarith
    have multiplied := Nat.mul_le_mul_left capacity (show bodyWords + 169 * width entry state capacity + 130 ≤ bodyWords + 169 * width entry state (capacity + 1) + 130 by omega)
    simp only [code, nonemptyCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq,
      WordIO.Code.descriptionWords_compute, WordIO.Code.descriptionWords_branch, selectSlice_descriptionWords]
    have loadWords : descriptionWords (.memLoad 1 0 0 : Stmt w) = 4 := rfl
    rw [loadWords]
    dsimp only [codeBudget] at ih ⊢
    rw [Nat.add_mul, Nat.one_mul]
    dsimp only [ListFold.prepareWords, width] at prepared multiplied ih ⊢
    nlinarith

theorem names (entry state capacity : Nat) {slots : Nat} (bodyNames : WordIO.NamesAccounted (body.lower port) slots) :
    WordIO.NamesAccounted ((code body (Interactive.savedBuffer port body) entry state capacity).lower port) slots := by
  induction capacity with
  | zero => exact WordIO.NamesAccounted.compute (selectSlice_names _ _ slots)
  | succ capacity ih =>
    exact (WordIO.NamesAccounted.compute (loadTag_names slots)).seq
      (((WordIO.NamesAccounted.compute (ListFold.prepare_names _ _ _ _ slots)).seq
        ((Interactive.retain_names port bodyNames _ _ _).seq
          ((WordIO.NamesAccounted.compute (Reorder.names _ _ _ slots)).seq ih))).branch
        (WordIO.NamesAccounted.compute (selectSlice_names _ _ slots)))

theorem buffers (entry state capacity : Nat) :
    ((code body (Interactive.savedBuffer port body) entry state capacity).lower port).memBound ≤ max 2 (body.lower port).memBound + 1 := by
  induction capacity with
  | zero => exact (selectSlice_buffers _ _).trans (by omega)
  | succ capacity ih =>
    have prepared := ListFold.prepare_buffers (w := w) entry state 0 capacity
    have retained := Interactive.retain_buffers port body (entry + state) state (1 + capacity * entry)
    have reordered := Reorder.buffers (w := w) state (1 + capacity * entry) 0
    have stopped := selectSlice_buffers (w := w) (1 + (capacity + 1) * entry) state
    simp only [code, nonemptyCode, continuation, Interactive.Code.lower, WordIO.Code.memBound, Stmt.memBound]
    omega

variable {A B : Type} (entry : Representation w A) (state : Representation w B) (hw : 16 < 2 ^ w)
    (argFits : entry.encoding.words + state.encoding.words < 2 ^ w)

include hw argFits in
theorem descriptionFits (bodyFits : (body.lower port).DescriptionFits)
    (nameFits : Interactive.savedBuffer port body < 2 ^ w) (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.encoding.words + state.encoding.words < 2 ^ w) :
    ((code body (Interactive.savedBuffer port body) entry.encoding.words state.encoding.words capacity).lower port).DescriptionFits := by
  induction capacity with
  | zero => exact .compute (selectSlice_descriptionFits _ _ hw state.fits)
  | succ capacity ih =>
    have prepared := ListFold.prepare_descriptionFits (w := w) entry.encoding.words state.encoding.words 0 capacity hw
      (by simpa [ListFold.prepareWords] using storageFits)
    have retained := Interactive.retain_descriptionFits port body (Interactive.savedBuffer port body)
      (entry.encoding.words + state.encoding.words) state.encoding.words (1 + capacity * entry.encoding.words)
      hw bodyFits nameFits argFits (by nlinarith) (by nlinarith)
    have reordered := Assembly.code_descriptionFits (Reorder.operands (w := w) state.encoding.words (1 + capacity * entry.encoding.words) 0)
      hw (by rw [Reorder.operands_length]; nlinarith) (Reorder.operands_names _ _ _)
    have smallerCount : capacity < 2 ^ w := by omega
    have smallerStorage : 1 + capacity * entry.encoding.words + state.encoding.words < 2 ^ w := by nlinarith
    have following := ih smallerCount smallerStorage
    have positive := width_pos hw
    exact WordIO.Code.DescriptionFits.seq (w := w) hw
      (.compute (code := (.memLoad 1 0 0 : Stmt w)) (by simp [DescriptionFits, description]; omega))
      (.branch (w := w) (condition := 1) hw (Nat.one_lt_two_pow (width_pos hw).ne')
        (.seq hw (.compute prepared) (.seq hw retained (.seq hw (.compute reordered) following)))
        (.compute (selectSlice_descriptionFits _ _ hw state.fits)))

variable (invariant : Nat → B → Prop) {f : A × B → OracleComp spec B}
    (bodyRefines : ∀ remaining, Interactive.RefinesOn (fun value : A × B => invariant (remaining + 1) value.2)
      port .unit (entry.prod state argFits) state f body)
    (preserves : ∀ remaining value, invariant (remaining + 1) value.2 → ∀ answer ∈ support (f value), invariant remaining answer)
    {bodyTime bodyWords slots : Nat}
    (bodyBound : ∀ remaining, Interactive.TimeBoundOn (fun value : A × B => invariant (remaining + 1) value.2)
      port .unit (entry.prod state argFits) body bodyTime)
    (bodyWordsBound : (body.lower port).descriptionWords ≤ bodyWords)
    (bodyNames : WordIO.NamesAccounted (body.lower port) slots)

include hw bodyRefines preserves bodyBound bodyWordsBound bodyNames in
theorem resources (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.encoding.words + state.encoding.words < 2 ^ w)
    (tape : RandomTape w) (value : BoundedList A capacity × B) (valid : invariant value.1.val.length value.2)
    (before : State w) (holds : (frame entry state capacity countFits storageFits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code body (Interactive.savedBuffer port body) entry.encoding.words state.encoding.words capacity).execute port .unit tape before)) :
    finished.time ≤ timeBudget entry.encoding.words state.encoding.words capacity bodyTime ∧
    ∃ answer ∈ support (denote f value), state.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((code body (Interactive.savedBuffer port body) entry.encoding.words state.encoding.words capacity).lower port)
          before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((code body (Interactive.savedBuffer port body) entry.encoding.words state.encoding.words capacity).lower port).registerSlots) ∧
          between.SupportBound (max buffers ((code body (Interactive.savedBuffer port body) entry.encoding.words state.encoding.words capacity).lower port).memBound) ∧ between.WellFormed ∧
          (((code body (Interactive.savedBuffer port body) entry.encoding.words state.encoding.words capacity).lower port).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code body (Interactive.savedBuffer port body) entry.encoding.words state.encoding.words capacity).lower port).memBound) ≤
              5 * codeBudget entry.encoding.words state.encoding.words capacity bodyWords + 4 * slots + registers + 3 * buffers +
                before.liveMem buffers + timeBudget entry.encoding.words state.encoding.words capacity bodyTime := by
  have refined := refines entry state hw argFits port invariant bodyRefines preserves capacity countFits storageFits
  have bounded := time_bound entry state hw argFits port invariant bodyRefines preserves bodyBound capacity countFits storageFits
  have stored := code_bound port body entry.encoding.words state.encoding.words capacity bodyWordsBound
  have generated := names port body entry.encoding.words state.encoding.words capacity bodyNames
  have nameBound : WordIO.NamesBound
      ((code body (Interactive.savedBuffer port body) entry.encoding.words state.encoding.words capacity).lower port)
      (slots + codeBudget entry.encoding.words state.encoding.words capacity bodyWords) :=
    ⟨generated.registers.trans (Nat.add_le_add_left stored slots), generated.buffers.trans (Nat.add_le_add_left stored slots)⟩
  obtain ⟨time, answer, supported, represented, execution, memory⟩ :=
    refined.resources bounded stored nameBound tape value valid before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨time, answer, supported, represented, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, limit⟩ := memory between visited
  refine ⟨registerBound, bufferBound, wellFormed, ?_⟩
  push_cast at limit ⊢
  omega

end Signatures.Runtime.CaliperBackend.InteractiveFold
