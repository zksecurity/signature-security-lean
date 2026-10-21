import Signatures.Runtime.Caliper.SchnorrROMFreshGuard

/-! Explicit polynomial bounds and a single execution accounting for stored
code, initial data, names and every visited buffer state of the guard. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.FreshGuard
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {F : Type} [DecidableEq F] (layout : Layouts w F)

omit [DecidableEq F] in
theorem fold_width : ListFold.width layout.entry.representation.encoding.words 3
    layout.scalar.representation.encoding.words layout.capacity ≤ 2 * layout.width := by
  rw [ListFold.width, Layouts.entry_words]
  unfold Layouts.width
  nlinarith

def polynomialTime := 16 * layout.width + 48 + layout.capacity * (10088 * layout.width + 1007)
def polynomialWords := 52 * layout.width + 215 + layout.capacity * (40338 * layout.width + 10115)
omit [DecidableEq F] in
theorem budget_bounds : timeBudget layout ≤ polynomialTime layout ∧ codeBudget layout ≤ polynomialWords layout := by
  have frameSize := (sizes layout).2.2
  have foldSize := fold_width layout
  have timeStep := Nat.mul_le_mul_left layout.capacity (show 10000 * layout.width + 1000 +
      44 * ListFold.width layout.entry.representation.encoding.words 3 layout.scalar.representation.encoding.words layout.capacity + 7 ≤
        10088 * layout.width + 1007 by omega)
  have wordsStep := Nat.mul_le_mul_left layout.capacity (show 40000 * layout.width + 10000 +
      169 * ListFold.width layout.entry.representation.encoding.words 3 layout.scalar.representation.encoding.words layout.capacity + 115 ≤
        40338 * layout.width + 10115 by omega)
  change 8 * (frame layout).representation.encoding.words + loopTime layout + (16 + 8) ≤ _ ∧
    (26 * (frame layout).representation.encoding.words + 14) + loopWords layout + (66 + 40 + 1) + 2 ≤ _
  unfold loopTime loopWords polynomialTime polynomialWords
  exact ⟨by omega, by omega⟩

theorem polynomial_bounded : (implementation layout).BoundedBy (polynomialTime layout) (polynomialWords layout) :=
  (bounded layout).mono (budget_bounds layout).1 (budget_bounds layout).2

theorem descriptionFits : DescriptionFits (implementation layout).program.code :=
  (implementation layout).program.description_fits

theorem resources (tape : RandomTape w) (value : (input layout).Value) (before : State w)
    (holds : (input layout).representation.Holds value before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout).program.code before after
      ((implementation layout).program.time value) net peak ∧
      layout.boolean.representation.Holds ⟨source value.val, (implementation layout).preserves value.val value.property⟩ after ∧
      (implementation layout).program.time value ≤ polynomialTime layout ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout).program.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots (implementation layout).program.code)) ∧
        between.SupportBound (max buffers (implementation layout).program.code.memBound) ∧ between.WellFormed ∧
        (staticWords (implementation layout).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout).program.code.memBound) ≤
            5 * polynomialWords layout + registers + 3 * buffers + before.liveMem buffers + polynomialTime layout := by
  simpa using
    (polynomial_bounded layout).memoryBound (names layout 0) tape value before holds registers buffers initialRegisters initialBuffers

end Signatures.Runtime.CaliperBackend.SchnorrROM.FreshGuard
