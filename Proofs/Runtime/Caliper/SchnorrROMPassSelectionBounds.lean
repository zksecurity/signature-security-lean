import Proofs.Runtime.Caliper.SchnorrROMPassSelection

/-! Complete selection resources include cutoff code, union redistribution and
both stored alternatives. No transcript scan or branch executes in the decoder. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.PassSelection
open Caliper BoundedSource
variable {w : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (ops : Handler.Operations config)
    (qH : Nat) (fits : qH + 1 < 2 ^ w) (budget : Handler.Budget config ops)

def timeBudget := (Selection.selectionBudget config ops qH fits budget).time + 32 * (input config).encoding.words + 20
def codeBudget := (Selection.selectionBudget config ops qH fits budget).words + 208 * (input config).encoding.words + 200
theorem time (value : Terminal.Output config) : (realizer config ops qH fits).time value ≤ timeBudget config ops qH fits budget := by
  have moved := SumContext.time (Pairing.unitRepresentation w) (ForgeryHash.result config)
    config.handler.store.representation config.sampler.wordFits (inputFits config) value
  change (distribute config).time value ≤ 24 * (input config).encoding.words + 2 at moved
  have sizes := widths config
  rcases value with ⟨cutoff | returned, saved⟩
  · have stopped : (PassSelection.cutoff config).time (cutoff, saved) ≤ 16 := ByteRoute.time _ _ _ _ _ _ _ _ _
    change (distribute config).time (.inl cutoff, saved) +
      (1 + (1 + ((selectSlice (w := w) 1 (cutoffInput config).encoding.words).staticTime .unit +
        (PassSelection.cutoff config).time (cutoff, saved)))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
    unfold timeBudget
    omega
  · have selected := (Selection.bounded config ops qH fits budget).time_le (Selection.represented config (returned, saved))
    change (Selection.realizer config ops qH fits).time (returned, saved) ≤ _ at selected
    change (distribute config).time (.inr returned, saved) +
      (1 + (1 + ((selectSlice (w := w) 1 (ForgeryHash.output config).encoding.words).staticTime .unit +
        (Selection.realizer config ops qH fits).time (returned, saved)))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
    unfold timeBudget
    omega
theorem words : descriptionWords (realizer config ops qH fits).code ≤ codeBudget config ops qH fits budget := by
  have moved := SumContext.words (Pairing.unitRepresentation w) (ForgeryHash.result config)
    config.handler.store.representation config.sampler.wordFits (inputFits config)
  change descriptionWords (distribute config).code ≤ 156 * (input config).encoding.words + 95 at moved
  have stopped : descriptionWords (cutoff config).code ≤ 66 := ByteRoute.codeWords _ _ _ _ _ _ _ _
  have selected := (Selection.bounded config ops qH fits budget).code_le
  change descriptionWords (Selection.realizer config ops qH fits).code ≤ _ at selected
  change descriptionWords ((distribute config).code ;; Dispatch.code (cutoff config).code
    (Selection.realizer config ops qH fits).code (cutoffInput config).encoding.words (ForgeryHash.output config).encoding.words) ≤ _
  rw [descriptionWords_seq, Dispatch.code_descriptionWords]
  have sizes := widths config
  unfold codeBudget
  omega
theorem bounded : (implementation config ops qH fits).BoundedBy
    (timeBudget config ops qH fits budget) (codeBudget config ops qH fits budget) :=
  ⟨fun value => time config ops qH fits budget value.val, words config ops qH fits budget⟩

theorem resources (tape : RandomTape w) (value : (Layout.all (input config)).Value) (before : State w)
    (holds : (Layout.all (input config)).representation.Holds value before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation config ops qH fits).program.code before after
      ((implementation config ops qH fits).program.time value) net peak ∧
      (Selection.result config).representation.Holds
        ⟨source config qH value.val, (implementation config ops qH fits).preserves value.val value.property⟩ after ∧
      (implementation config ops qH fits).program.time value ≤ (timeBudget config ops qH fits budget) ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation config ops qH fits).program.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots (implementation config ops qH fits).program.code)) ∧
        between.SupportBound (max buffers (implementation config ops qH fits).program.code.memBound) ∧ between.WellFormed ∧
        (staticWords (implementation config ops qH fits).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation config ops qH fits).program.code.memBound) ≤
            5 * (codeBudget config ops qH fits budget) + 4 * max 3 ops.slots + registers + 3 * buffers +
              before.liveMem buffers + (timeBudget config ops qH fits budget) :=
  (bounded config ops qH fits budget).memoryBound (names config ops qH fits) tape value before holds
    registers buffers initialRegisters initialBuffers

end Signatures.Runtime.CaliperBackend.SchnorrROM.PassSelection

namespace Signatures.Runtime.CaliperBackend.SchnorrROM.PassSelection
open Caliper BoundedSource
variable {w : Nat} {M F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
    [DecidableEq M] [DecidableEq G] (config : Signing.Enumerated.Configuration w M F G)

theorem source_original (cost : PrimitiveCosts) (qH : Nat) (value : Terminal.Output config) :
    Schnorr.asIndex qH (source config qH value) =
      (Terminal.observed config value).1.bind (fun returned =>
        Schnorr.selectPass (G₂ := G) (K := M) cost qH (returned, value.2.val.1)) := by
  rcases value with ⟨cutoff | returned, saved⟩
  · simp only [source, Schnorr.asIndex, Bool.false_eq_true, false_and, ↓reduceDIte,
      Terminal.observed, Sum.elim_inl, Option.bind_none]
  · exact Selection.source_selectPass cost qH (Selection.represented config (returned, saved)).val

end Signatures.Runtime.CaliperBackend.SchnorrROM.PassSelection
