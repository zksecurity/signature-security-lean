import Proofs.Runtime.Caliper.SchnorrROMReplayMatch

/-! Selection and slot matching include all copies of both pass results.
Time, stored code, dense names and visited memory belong to the same execution. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayMatch
open Caliper BoundedSource
variable {w : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (ops : Handler.Operations config)
    (qH : Nat) (indexFits : qH + 1 < 2 ^ w) (budget : Handler.Budget config ops)

def selectionTime := PassSelection.timeBudget config ops qH indexFits budget +
  8 * (ReplaySecond.first config).encoding.words + 8 * (Selection.result config).representation.encoding.words +
    12 * (frame config).encoding.words
def selectionWords := PassSelection.codeBudget config ops qH indexFits budget +
  26 * (ReplaySecond.first config).encoding.words + 26 * (Selection.result config).representation.encoding.words +
    39 * (frame config).encoding.words + 39
def checkTime := (Check.constructed config).budget.time + 8 * (argument config).representation.encoding.words +
  8 * (Selection.boolean config).representation.encoding.words + 12 * (frame config).encoding.words
def checkWords := (Check.constructed config).budget.words + 26 * (argument config).representation.encoding.words +
  26 * (Selection.boolean config).representation.encoding.words + 39 * (frame config).encoding.words + 39
def timeBudget := 8 * (prepared config).encoding.words + selectionTime config ops qH indexFits budget +
  8 * (checking config).encoding.words + checkTime config
def codeBudget := 26 * (prepared config).encoding.words + selectionWords config ops qH indexFits budget +
  26 * (checking config).encoding.words + checkWords config + 31

theorem selection_time (value) : (selection config ops qH indexFits).time value ≤ selectionTime config ops qH indexFits budget := by
  have retained := (PassSelection.realizer config ops qH indexFits).retain_time_unit_le (frame config)
    config.sampler.wordFits (selectionNameFits config ops qH indexFits) (prepared config).fits (selected config).fits value
  have body := PassSelection.time config ops qH indexFits budget value.1
  change _ ≤ _ + 8 * (ReplaySecond.first config).encoding.words + 8 * (Selection.result config).representation.encoding.words + 12 * _ at retained
  unfold selectionTime
  exact retained.trans (by omega)
theorem selection_words : descriptionWords (selection config ops qH indexFits).code ≤ selectionWords config ops qH indexFits budget := by
  have retained := (PassSelection.realizer config ops qH indexFits).retain_descriptionWords_le (by decide) (frame config)
    config.sampler.wordFits (selectionNameFits config ops qH indexFits) (prepared config).fits (selected config).fits
  have body := PassSelection.words config ops qH indexFits budget
  change _ ≤ _ + 26 * (ReplaySecond.first config).encoding.words + 26 * (Selection.result config).representation.encoding.words + 39 * _ + 39 at retained
  unfold selectionWords
  exact retained.trans (by omega)
omit [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G] in
theorem check_time (value) : (Check.retained config).time value ≤ checkTime config := by
  have retained := (Check.constructed config).implementation.program.retain_time_unit_le (frame config)
    config.sampler.wordFits (Check.nameFits config) (checking config).fits (output config).fits value
  have body := (Check.constructed config).bounded.time_le value.1
  unfold checkTime
  exact retained.trans (by omega)
omit [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G] in
theorem check_words : descriptionWords (Check.retained config).code ≤ checkWords config := by
  have retained := (Check.constructed config).implementation.program.retain_descriptionWords_le (by decide) (frame config)
    config.sampler.wordFits (Check.nameFits config) (checking config).fits (output config).fits
  have body := (Check.constructed config).bounded.code_le
  unfold checkWords
  exact retained.trans (by omega)
theorem time (value : Frame config) : (realizer config ops qH indexFits).time value ≤ timeBudget config ops qH indexFits budget := by
  have preparedBound : (prepare config).time value ≤ 8 * (prepared config).encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ _
  have selectedBound := selection_time config ops qH indexFits budget (value.1, value)
  have argumentsBound : (arguments config).time (selectionValue config ops qH indexFits value) ≤
      8 * (checking config).encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ _
  have checkedBound := check_time config (argumentValue config (selectionValue config ops qH indexFits value))
  change ((prepare config).time value + (selection config ops qH indexFits).time (value.1, value)) +
    (arguments config).time (selectionValue config ops qH indexFits value) +
    (Check.retained config).time (argumentValue config (selectionValue config ops qH indexFits value)) ≤ _
  unfold timeBudget
  omega
theorem words : descriptionWords (realizer config ops qH indexFits).code ≤ codeBudget config ops qH indexFits budget := by
  have preparedBound : descriptionWords (prepare config).code ≤ 26 * (prepared config).encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
  have selectedBound := selection_words config ops qH indexFits budget
  have argumentsBound : descriptionWords (arguments config).code ≤ 26 * (checking config).encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
  have checkedBound := check_words config
  change descriptionWords ((((prepare config).code ;; (selection config ops qH indexFits).code) ;; (arguments config).code) ;;
    (Check.retained config).code) ≤ _
  rw [descriptionWords_seq, descriptionWords_seq, descriptionWords_seq]
  unfold codeBudget
  omega
theorem bounded : (implementation config ops qH indexFits).BoundedBy
    (timeBudget config ops qH indexFits budget) (codeBudget config ops qH indexFits budget) :=
  ⟨fun value => time config ops qH indexFits budget value.val, words config ops qH indexFits budget⟩

theorem resources (tape : RandomTape w) (value : (Layout.all (frame config)).Value) (before : State w)
    (holds : (Layout.all (frame config)).representation.Holds value before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation config ops qH indexFits).program.code before after
      ((implementation config ops qH indexFits).program.time value) net peak ∧
      (Layout.all (output config)).representation.Holds ⟨source config qH value.val, trivial⟩ after ∧
      (implementation config ops qH indexFits).program.time value ≤ timeBudget config ops qH indexFits budget ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation config ops qH indexFits).program.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots (implementation config ops qH indexFits).program.code)) ∧
        between.SupportBound (max buffers (implementation config ops qH indexFits).program.code.memBound) ∧ between.WellFormed ∧
        (staticWords (implementation config ops qH indexFits).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation config ops qH indexFits).program.code.memBound) ≤
            5 * codeBudget config ops qH indexFits budget + 4 * max 3 ops.slots + registers + 3 * buffers +
              before.liveMem buffers + timeBudget config ops qH indexFits budget :=
  (bounded config ops qH indexFits budget).memoryBound (names config ops qH indexFits) tape value before holds
    registers buffers initialRegisters initialBuffers

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayMatch
