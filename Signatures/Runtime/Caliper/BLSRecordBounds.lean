import Signatures.Runtime.Caliper.BLSRecord
import Signatures.Runtime.Caliper.ImplementationMemory

/-! Derived budgets for transcript recording. No primitive routine, finished
update, or free list copy is assumed. All bounds depend on stored widths. -/

namespace Signatures.Runtime.CaliperBackend.BLSRecord

open Caliper BoundedSource

variable {w : Nat} {M G : Type} (layout : Layouts w M G)

theorem entry_bounded (signing : Bool) : (entry layout signing).BoundedBy
    (8 * layout.entryWords) (26 * layout.entryWords + 14) :=
  (Implementation.first_boundedBy layout.entry layout.transcript layout.wordFits
    layout.unrestrictedInput.representation.fits).restrictInput (layout.room signing)

theorem log_bounded (signing selected : Bool) : (log layout signing selected).BoundedBy
    (24 * layout.logWords) (78 * layout.logWords + 29) := by
  cases selected
  · apply (((Implementation.second_boundedBy layout.entry layout.transcript layout.wordFits layout.unrestrictedInput.representation.fits).then
      (Implementation.first_boundedBy layout.log layout.log layout.wordFits layout.transcript.representation.fits)).restrictInput (layout.room signing)).mono
    all_goals simp only [Layouts.transcript_words, Layouts.log_words]; omega
  · apply (((Implementation.second_boundedBy layout.entry layout.transcript layout.wordFits layout.unrestrictedInput.representation.fits).then
      (Implementation.second_boundedBy layout.log layout.log layout.wordFits layout.transcript.representation.fits)).restrictInput (layout.room signing)).mono
    all_goals simp only [Layouts.transcript_words, Layouts.log_words]; omega

theorem point_bounded (signing : Bool) : (point layout signing).BoundedBy
    (8 * layout.entryWords + 8 * layout.point.representation.encoding.words)
    (26 * layout.entryWords + 26 * layout.point.representation.encoding.words + 29) := by
  apply ((entry_bounded layout signing).then (Implementation.second_boundedBy _ _ _ _)).mono <;> omega

theorem arguments_bounded (signing : Bool) : (arguments layout signing).BoundedBy
    (96 * layout.entryWords + 144 * layout.logWords) (312 * layout.entryWords + 468 * layout.logWords + 167) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (entry_bounded layout signing) (log_bounded layout signing signing)).mono
  all_goals simp only [Layouts.input_words, Layouts.entry_words, Layouts.log_words, Layouts.width]; omega

theorem updated_bounded (signing : Bool) : (updated layout signing).BoundedBy
    (96 * layout.entryWords + 160 * layout.logWords + 5) (312 * layout.entryWords + 520 * layout.logWords + 221) := by
  apply (((arguments_bounded layout signing).restrictOutput (fun value => value.2.length ≤ layout.capacityPred)
    (fun _ valid => valid.2)).then (ListData.fixedCons_boundedBy _ _ _ _ _)).mono
  all_goals simp only [Layouts.entry_words]; dsimp only [Layouts.logWords]; omega

def recordTime : Nat := 148 * layout.entryWords + 340 * layout.logWords + 5
def recordWords : Nat := 481 * layout.entryWords + 1105 * layout.logWords + 374
def timeBudget : Nat := 208 * layout.entryWords + 44 * layout.point.representation.encoding.words + 476 * layout.logWords + 5
def codeBudget : Nat := 676 * layout.entryWords + 143 * layout.point.representation.encoding.words + 1547 * layout.logWords + 527

theorem record_bounded (signing : Bool) : (record layout signing).BoundedBy (recordTime layout) (recordWords layout) := by
  cases signing
  · apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (updated_bounded layout false) (log_bounded layout false true)).mono
    all_goals simp only [Layouts.input_words, Layouts.log_words, Layouts.width, recordTime, recordWords]; omega
  · apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (log_bounded layout true false) (updated_bounded layout true)).mono
    all_goals simp only [Layouts.input_words, Layouts.log_words, Layouts.width, recordTime, recordWords]; omega

theorem delivered_bounded (signing : Bool) : (delivered layout signing).BoundedBy (timeBudget layout) (codeBudget layout) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (point_bounded layout signing) (record_bounded layout signing)).mono
  all_goals simp only [Layouts.input_words, Layouts.transcript_words, Layouts.width, recordTime, recordWords, timeBudget, codeBudget]; omega

variable (names : Nat)

theorem entry_names (signing : Bool) : NamesAccounted (entry layout signing).program.code names :=
  Implementation.first_names layout.entry layout.transcript layout.wordFits layout.unrestrictedInput.representation.fits names

theorem log_names (signing selected : Bool) : NamesAccounted (log layout signing selected).program.code names := by
  cases selected
  · exact (Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)
  · exact (Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _)

theorem point_names (signing : Bool) : NamesAccounted (point layout signing).program.code names :=
  (entry_names layout names signing).seq (Implementation.second_names _ _ _ _ _)

theorem arguments_names (signing : Bool) : NamesAccounted (arguments layout signing).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (entry_names layout names signing) (log_names layout names signing signing)

theorem updated_names (signing : Bool) : NamesAccounted (updated layout signing).program.code names :=
  (arguments_names layout names signing).seq (ListData.fixedCons_names _ _ _ _ _ _)

theorem record_names (signing : Bool) : NamesAccounted (record layout signing).program.code names := by
  cases signing
  · exact Implementation.pair_names _ _ _ _ _ _ _ _ (updated_names layout names false) (log_names layout names false true)
  · exact Implementation.pair_names _ _ _ _ _ _ _ _ (log_names layout names true false) (updated_names layout names true)

theorem delivered_names (signing : Bool) : NamesAccounted (delivered layout signing).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (point_names layout names signing) (record_names layout names signing)

/-- The returned reply and source transcript update are represented by the same
execution whose full memory is bounded, including the caller's spare capacity. -/
theorem memoryBound (signing : Bool) (tape : RandomTape w) (value : (layout.input signing).Value) (before : State w)
    (represented : (layout.input signing).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (delivered layout signing).program.code before after
        ((delivered layout signing).program.time value) net peak ∧
      layout.output.representation.Holds
        ⟨(value.val.1.2, LazyAGM.record signing value.val.1.1 value.val.1.2 value.val.2),
          (delivered layout signing).preserves value.val value.property⟩ after ∧
      (delivered layout signing).program.time value ≤ timeBudget layout ∧
      ∀ between, (Caliper.Reaches .unit tape (delivered layout signing).program.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots (delivered layout signing).program.code)) ∧
        between.SupportBound (max buffers (delivered layout signing).program.code.memBound) ∧ between.WellFormed ∧
        (staticWords (delivered layout signing).program.code registers buffers : Int) +
          between.liveMem (max buffers (delivered layout signing).program.code.memBound) ≤
            5 * codeBudget layout + registers + 3 * buffers + before.liveMem buffers + timeBudget layout := by
  simpa only [Nat.cast_zero, mul_zero, add_zero] using
    (delivered_bounded layout signing).memoryBound (delivered_names layout 0 signing)
      tape value before represented registers buffers initialRegisters initialBuffers

end Signatures.Runtime.CaliperBackend.BLSRecord
