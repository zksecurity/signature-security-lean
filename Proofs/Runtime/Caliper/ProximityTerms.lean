import Proofs.Runtime.Caliper.ProximityTermsAssembly

/-! Complete executed Proximity term generation. Time and stored code are
linear in the output's declared word width, including every repeated slot.
The same execution has a bound on total memory at all intermediate states. -/
namespace Signatures.Runtime.CaliperBackend.ProximityTerms
open Caliper BoundedSource Assembly
variable {w dimension : Nat} {F K : Type} [One F]
    (layout : Layouts w F K dimension) (oneValid : layout.scalar.valid (1 : F))

def implementation : Implementation .unit layout.input layout.output value where
  preserves := preserves layout oneValid
  program := Assembly.realizer .unit (by decide) _ _ _ (operands layout oneValid) layout.wordFits
    (operands_length layout oneValid)
    (by
      intro operand member
      have source := operands_sources layout oneValid operand member
      cases operand with
      | literal _ => trivial
      | read buffer offset =>
        change buffer + 1 ≤ 1 at source
        change buffer < 2 ^ w
        exact (Nat.lt_of_succ_le source).trans_le Nat.one_le_two_pow)
    (operands_valid layout oneValid) (operands_values layout oneValid)

def timeBudget : Nat := 8 * layout.width
def codeBudget : Nat := 26 * layout.width + 14

theorem bounded : (implementation layout oneValid).BoundedBy (timeBudget layout) (codeBudget layout) := by
  constructor
  · intro input
    have bound := code_time_unit_le (operands layout oneValid)
    rw [operands_length, layout.output_words] at bound
    exact bound
  · have bound := code_descriptionWords_le (operands layout oneValid)
    rw [operands_length, layout.output_words] at bound
    exact bound

theorem buffers : (implementation layout oneValid).program.code.memBound ≤ 2 :=
  (code_names (operands layout oneValid) 1 (operands_sources layout oneValid)).2

theorem names (slots : Nat) : NamesAccounted (implementation layout oneValid).program.code slots :=
  code_namesAccounted (operands layout oneValid) slots (operands_sources layout oneValid)

theorem resources (tape : RandomTape w) (input : layout.input.Value) (before : State w)
    (holds : layout.input.representation.Holds input before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout oneValid).program.code before after
      ((implementation layout oneValid).program.time input) net peak ∧
      layout.output.representation.Holds
        ⟨value input.val, (implementation layout oneValid).preserves input.val input.property⟩ after ∧
      (implementation layout oneValid).program.time input ≤ timeBudget layout ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout oneValid).program.code before between ∨ between = after) →
        (staticWords (implementation layout oneValid).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout oneValid).program.code.memBound) ≤
            5 * codeBudget layout + registers + 3 * buffers + before.liveMem buffers + timeBudget layout := by
  obtain ⟨after, net, peak, execution, output, elapsed, memory⟩ :=
    (bounded layout oneValid).memoryBound (names layout oneValid 0) tape input before holds
      registers buffers initialRegisters initialBuffers
  exact ⟨after, net, peak, execution, output, elapsed, fun between visited => by
    simpa using (memory between visited).2.2.2⟩

end Signatures.Runtime.CaliperBackend.ProximityTerms
