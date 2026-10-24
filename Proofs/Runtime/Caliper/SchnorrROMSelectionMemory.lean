import Proofs.Runtime.Caliper.SchnorrROMSelectionSource

/-! Selection correctness and all-visited memory are properties of the same
execution, including stored code, dense names and caller-owned initial data. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Selection
open Caliper BoundedSource
variable {w : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (ops : Handler.Operations config)
    (qH : Nat) (fits : qH + 1 < 2 ^ w) (budget : Handler.Budget config ops)

theorem resources (tape : RandomTape w) (value : (input config).Value) (before : State w)
    (holds : (input config).representation.Holds value before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation config ops qH fits).program.code before after
      ((implementation config ops qH fits).program.time value) net peak ∧
      (result config).representation.Holds
        ⟨source qH value.val, (implementation config ops qH fits).preserves value.val value.property⟩ after ∧
      (implementation config ops qH fits).program.time value ≤ (selectionBudget config ops qH fits budget).time ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation config ops qH fits).program.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots (implementation config ops qH fits).program.code)) ∧
        between.SupportBound (max buffers (implementation config ops qH fits).program.code.memBound) ∧ between.WellFormed ∧
        (staticWords (implementation config ops qH fits).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation config ops qH fits).program.code.memBound) ≤
            5 * (selectionBudget config ops qH fits budget).words + 4 * ops.slots + registers + 3 * buffers +
              before.liveMem buffers + (selectionBudget config ops qH fits budget).time :=
  (bounded config ops qH fits budget).memoryBound (names config ops qH fits) tape value before holds
    registers buffers initialRegisters initialBuffers

end Signatures.Runtime.CaliperBackend.SchnorrROM.Selection
