import Proofs.Runtime.Caliper.BLSRecordLayout

/-! Executed recording of a delivered BLS reply. Selection, shared-input copies,
fixed-capacity insertion and restoration of output order all use Caliper code. -/

namespace Signatures.Runtime.CaliperBackend.BLSRecord

open Caliper BoundedSource

variable {w : Nat} {M G : Type} (layout : Layouts w M G)

def entry (signing : Bool) : Implementation .unit (layout.input signing) layout.entry Prod.fst :=
  (Implementation.first (by decide) layout.entry layout.transcript layout.wordFits _).restrictInput (layout.room signing)

def log (signing selected : Bool) : Implementation .unit (layout.input signing) layout.log
    (fun value => if selected then value.2.2 else value.2.1) := by
  cases selected
  · exact ((Implementation.second (by decide) layout.entry layout.transcript layout.wordFits _).then
      (Implementation.first (by decide) layout.log layout.log layout.wordFits _)).restrictInput (layout.room signing)
  · exact ((Implementation.second (by decide) layout.entry layout.transcript layout.wordFits _).then
      (Implementation.second (by decide) layout.log layout.log layout.wordFits _)).restrictInput (layout.room signing)

def point (signing : Bool) : Implementation .unit (layout.input signing) layout.point (fun value => value.1.2) :=
  (entry layout signing).then (Implementation.second (by decide) layout.message layout.point layout.wordFits _)

theorem entry_buffers (signing : Bool) : (entry layout signing).program.code.memBound ≤ 2 :=
  Implementation.first_buffers (cost := .unit) (by decide) layout.entry layout.transcript layout.wordFits layout.unrestrictedInput.representation.fits
theorem log_buffers (signing selected : Bool) : (log layout signing selected).program.code.memBound ≤ 2 := by
  cases selected
  · exact max_le (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)
  · exact max_le (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _)
theorem point_buffers (signing : Bool) : (point layout signing).program.code.memBound ≤ 2 :=
  max_le (entry_buffers layout signing) (Implementation.second_buffers _ _ _ _ _)

def arguments (signing : Bool) : Implementation .unit (layout.input signing) layout.entryLog
    (fun value => (value.1, if signing then value.2.2 else value.2.1)) :=
  (entry layout signing).pair (log layout signing signing) (by decide) layout.wordFits
    (layout.nameFits _ (entry_buffers layout signing) (by decide))
    (layout.nameFits _ (log_buffers layout signing signing) (by decide))
    (layout.fits_of_le (by rw [Layouts.input_words]; omega))
    (layout.fits_of_le (by rw [Layouts.entry_words, Layouts.input_words]; dsimp only [Layouts.width]; omega)) _

theorem arguments_buffers (signing : Bool) : (arguments layout signing).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (entry_buffers layout signing) (log_buffers layout signing signing)

def updated (signing : Bool) : Implementation .unit (layout.input signing) layout.log
    (fun value => value.1 :: (if signing then value.2.2 else value.2.1)) :=
  ((arguments layout signing).restrictOutput (fun value => value.2.length ≤ layout.capacityPred)
    (fun _ valid => valid.2)).then
      (ListData.fixedCons .unit (by decide) layout.entry layout.capacityPred layout.wordFits layout.countFits layout.fixedConsFits)

theorem updated_buffers (signing : Bool) : (updated layout signing).program.code.memBound ≤ 3 :=
  max_le (arguments_buffers layout signing) ((ListData.fixedCons_buffers _ _ _ _ _ _ _).trans (by decide))

def record (signing : Bool) : Implementation .unit (layout.input signing) layout.transcript
    (fun value => LazyAGM.record signing value.1.1 value.1.2 value.2) := by
  cases signing
  · exact (updated layout false).pair (log layout false true) (by decide) layout.wordFits
      (layout.nameFits _ (updated_buffers layout false) (by decide))
      (layout.nameFits _ (log_buffers layout false true) (by decide))
      (layout.fits_of_le (by rw [Layouts.input_words]; omega))
      (layout.fits_of_le (by rw [Layouts.log_words, Layouts.input_words]; dsimp only [Layouts.width]; omega)) _
  · exact (log layout true false).pair (updated layout true) (by decide) layout.wordFits
      (layout.nameFits _ (log_buffers layout true false) (by decide))
      (layout.nameFits _ (updated_buffers layout true) (by decide))
      (layout.fits_of_le (by rw [Layouts.input_words]; omega))
      (layout.fits_of_le (by rw [Layouts.log_words, Layouts.input_words]; dsimp only [Layouts.width]; omega)) _

theorem record_buffers (signing : Bool) : (record layout signing).program.code.memBound ≤ 4 := by
  cases signing
  · exact Implementation.pair_buffers _ _ _ _ _ _ _ _ (updated_buffers layout false) (log_buffers layout false true)
  · exact Implementation.pair_buffers _ _ _ _ _ _ _ _ (log_buffers layout true false) (updated_buffers layout true)

def delivered (signing : Bool) : Implementation .unit (layout.input signing) layout.output
    (fun value => (value.1.2, LazyAGM.record signing value.1.1 value.1.2 value.2)) :=
  (point layout signing).pair (record layout signing) (by decide) layout.wordFits
    (layout.nameFits _ (point_buffers layout signing) (by decide))
    (layout.nameFits _ (record_buffers layout signing) (by decide))
    (layout.fits_of_le (by rw [Layouts.input_words]; omega))
    (layout.fits_of_le (by rw [Layouts.input_words]; dsimp only [Layouts.width, Layouts.entryWords]; omega)) _

theorem delivered_buffers (signing : Bool) : (delivered layout signing).program.code.memBound ≤ 5 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (point_buffers layout signing) (record_buffers layout signing)

end Signatures.Runtime.CaliperBackend.BLSRecord
