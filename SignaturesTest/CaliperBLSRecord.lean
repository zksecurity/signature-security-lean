import Signatures.Runtime.Caliper.BLSRecordBounds
import Signatures.Runtime.Caliper.BLSRecordReachability
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend
open Signatures.Runtime.CaliperBackend.BoundedSource Model.LazyAGM BLS.LazyAGM.Reduction

namespace SignaturesTest.CaliperBLSRecord

-- Infinite message type, with only encountered messages required to fit.
private def layout : BLSRecord.Layouts 8 Nat (Word 8) where
  message := Layout.counter 8 256 (by decide) (by decide)
  point := Layout.all (wordRepresentation 8 (by decide))
  capacityPred := 1
  wordFits := by decide
  countFits := by decide
  storageFits := by decide

private theorem valid_iff (signing : Bool) (message : Nat) (reply : Word 8) (tr : BLSRecord.Transcript Nat (Word 8)) :
    (layout.input signing).valid ((message, reply), tr) ↔
      (message < 256 ∧ (tr.1.length ≤ 2 ∧ ∀ entry ∈ tr.1, entry.1 < 256) ∧
        (tr.2.length ≤ 2 ∧ ∀ entry ∈ tr.2, entry.1 < 256)) ∧ (if signing then tr.2 else tr.1).length ≤ 1 := by
  change ((message < 256 ∧ True) ∧ (tr.1.length ≤ 2 ∧ ∀ entry ∈ tr.1, entry.1 < 256 ∧ True) ∧
    (tr.2.length ≤ 2 ∧ ∀ entry ∈ tr.2, entry.1 < 256 ∧ True)) ∧ _ ↔ _
  simp only [and_true]
  rfl

private def hashInput : (layout.input false).Value :=
  ⟨((7, 11), [(2, 3)], [(4, 5), (6, 7)]), by rw [valid_iff]; decide⟩
private def signInput : (layout.input true).Value :=
  ⟨((7, 11), [(1, 2), (3, 4)], [(6, 7)]), by rw [valid_iff]; decide⟩
private def repeatedInput : (layout.input false).Value :=
  ⟨((7, 11), [(7, 11)], []), by rw [valid_iff]; decide⟩
private def emptyInput : (layout.input false).Value :=
  ⟨((7, 11), [], []), by rw [valid_iff]; decide⟩

private def observe (signing : Bool) (value : (layout.input signing).Value) :=
  let initial := (layout.input signing).representation.initial value
  let before := { initial with
    regs := fun register => if register = 200 then 99 else initial.regs register
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 4 else initial.caps buffer
    tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 10000 (BLSRecord.delivered layout signing).program.code before).map
    (fun (state, _, _, _) => (state.bufs 0, state.bufs 200, state.caps 200, state.regs 200, state.tapePos))

-- The unselected full log is retained, and the selected log keeps capacity two.
example : observe false hashInput = some (#[11, 2, 7, 11, 2, 3, 2, 4, 5, 6, 7], #[77], 4, 99, 9) := by decide +kernel
example : observe true signInput = some (#[11, 2, 1, 2, 3, 4, 2, 7, 11, 6, 7], #[77], 4, 99, 9) := by decide +kernel
-- Every delivered reply is recorded, even when it repeats a prior cache hit.
example : observe false repeatedInput = some (#[11, 2, 7, 11, 7, 11, 0, 0, 0, 0, 0], #[77], 4, 99, 9) := by decide +kernel
example : observe false emptyInput = some (#[11, 1, 7, 11, 0, 0, 0, 0, 0, 0, 0], #[77], 4, 99, 9) := by decide +kernel

example : ¬ (layout.input false).valid ((7, 11), [(1, 2), (3, 4)], []) := by rw [valid_iff]; decide
example : ¬ (layout.input true).valid ((7, 11), [], [(1, 2), (3, 4)]) := by rw [valid_iff]; decide
example : ¬ (layout.input false).valid ((256, 11), [], []) := by rw [valid_iff]; decide
example : ¬ (layout.input false).valid ((7, 11), [(256, 0)], []) := by rw [valid_iff]; decide

example (signing : Bool) : (BLSRecord.delivered layout signing).BoundedBy 2845 9757 := BLSRecord.delivered_bounded layout signing
example (signing : Bool) : (BLSRecord.delivered layout signing).program.code.memBound ≤ 5 := BLSRecord.delivered_buffers layout signing
example (signing : Bool) : DescriptionFits (BLSRecord.delivered layout signing).program.code :=
  (BLSRecord.delivered layout signing).program.description_fits
example (signing : Bool) : staticWords (BLSRecord.delivered layout signing).program.code 201 201 ≤ 49589 :=
  (BLSRecord.delivered_bounded layout signing).staticMemory (BLSRecord.delivered_names layout 0 signing) 201 201

private def hash (value : Fin 2) : Word 8 := if value = 0 then 11 else 13
private def sign (value : Fin 2) : Word 8 := if value = 0 then 17 else 19
private def nextMessage (reply : Word 8) : Nat := if reply = 11 then 7 else 8
private def tail (reply : Word 8) : OracleComp (advSpec Nat Nat (Word 8)) (Word 8) :=
  queryBind (.inr (nextMessage reply)) Pure.pure
private def adaptive : OracleComp (advSpec Nat Nat (Word 8)) (Word 8) := queryBind (.inl (.inr 7)) tail

private theorem adaptive_queries : AllQueriesSatisfy adaptive (BLSRecord.allowedQuery layout) := by
  change (7 < 256) ∧ ∀ reply : Word 8, (nextMessage reply < 256) ∧ ∀ _ : Word 8, True
  refine ⟨by decide, fun reply => ⟨?_, fun _ => trivial⟩⟩
  unfold nextMessage
  split <;> decide
private theorem adaptive_bound : IsTotalQueryBound adaptive 2 := by
  change (0 < 2) ∧ ∀ _ : Word 8, (0 < 1) ∧ ∀ _ : Word 8, True
  exact ⟨by decide, fun _ => ⟨by decide, fun _ => trivial⟩⟩

private theorem firstPath (value : Fin 2) :
    SourcePrefix (LazyAGM.listOracle hash sign) adaptive ([], [], []) (tail (hash value))
      ([(7, value)], [(7, hash value)], []) 1 := by
  apply SourcePrefix.step (handler := LazyAGM.listOracle hash sign)
    (query := .inl (.inr 7)) (next := tail) SourcePrefix.start (hash value, [(7, value)], [(7, hash value)], [])
  rw [LazyAGM.listOracle_hash]
  simp only [support_map, Set.mem_image]
  refine ⟨(value, [(7, value)]), ?_, rfl⟩
  rw [privateListOracle_lookup]
  simp only [List.lookup_nil, support_map, Set.mem_image]
  exact ⟨value, mem_support_uniformSample (Fin 2), rfl⟩

private theorem ready (value : Fin 2) :
    (layout.input true).valid ((nextMessage (hash value), sign value), [(7, hash value)], []) :=
  BLSRecord.ready layout hash sign (fun _ => trivial) (fun _ => trivial) adaptive_queries
    (by simp [BLSRecord.entriesFit]) adaptive_bound (by decide) true (nextMessage (hash value)) Pure.pure
    (firstPath value) (sign value) trivial

private def runTail (value : Fin 2) := observe true ⟨_, ready value⟩
example : runTail 0 = some (#[17, 1, 7, 11, 0, 0, 1, 7, 17, 0, 0], #[77], 4, 99, 9) := by decide +kernel
example : runTail 1 = some (#[19, 1, 7, 13, 0, 0, 1, 8, 19, 0, 0], #[77], 4, 99, 9) := by decide +kernel

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``BLSRecord.record_bounded, ``BLSRecord.delivered_bounded, ``BLSRecord.record_names, ``BLSRecord.delivered_names,
      ``BLSRecord.record_buffers, ``BLSRecord.delivered_buffers, ``BLSRecord.memoryBound,
      ``BLSRecord.record_entries, ``BLSRecord.reply_entries, ``BLSRecord.query_entries, ``BLSRecord.prefix_entries,
      ``BLSRecord.ready, ``firstPath, ``ready] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperBLSRecord
