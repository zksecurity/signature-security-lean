import Signatures.Runtime.Caliper.OOPSTerms

/-! OOPS generation budgets include the multiplication code, every repeated
power stage, saved-topic copies and final term assembly. Only multiplication's
local bounds are supplied; all generator overhead and memory are derived. -/
namespace Signatures.Runtime.CaliperBackend.OOPSTerms
open Caliper BoundedSource Assembly
variable {w degree : Nat} {F K : Type} [Mul F] [One F]
    (layout : Layouts w F K degree) (oneValid : layout.scalar.valid (1 : F))
    (mul : Implementation .unit layout.powers.input layout.scalar (fun input => input.1 * input.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots)
    (reserve : Powers.baseSlots slots + degree < 2 ^ w)

omit [Mul F] [One F] in
theorem duplicate_bounded : (duplicate layout).BoundedBy
    (16 * layout.scalar.representation.encoding.words) (52 * layout.scalar.representation.encoding.words + 14) := by
  constructor
  · intro input
    have bound := code_time_unit_le (reads (w := w) 0 0 layout.scalar.representation.encoding.words ++
      reads 0 0 layout.scalar.representation.encoding.words)
    simp only [List.length_append, reads_length] at bound
    exact bound.trans (by omega)
  · have bound := code_descriptionWords_le (reads (w := w) 0 0 layout.scalar.representation.encoding.words ++
      reads 0 0 layout.scalar.representation.encoding.words)
    simp only [List.length_append, reads_length] at bound
    exact bound.trans (by omega)

omit [Mul F] [One F] in
theorem duplicate_names (names : Nat) : NamesAccounted (duplicate layout).program.code names :=
  code_namesAccounted _ names ((sourcesBound_append _ _ _).mpr
    ⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩)

variable {mulTime mulWords : Nat} (budget : mul.BoundedBy mulTime mulWords)

omit [One F] in
include budget in
theorem generated_bounded : (generated layout mul mulBuffers reserve).BoundedBy
    (Powers.timeBudget layout.powers mulTime degree + 24 * layout.width)
    (Powers.codeBudget layout.powers mulWords degree + 78 * layout.width + 32) := by
  apply (((Implementation.first_boundedBy _ _ _ _).then (duplicate_bounded layout)).then
    (Powers.bounded layout.powers reserve mul mulBuffers budget degree (Nat.le_refl _))).mono
  all_goals have := layout.parts; omega

omit [One F] in
include budget in
theorem prepare_bounded : (prepare layout mul mulBuffers reserve).BoundedBy
    (Powers.timeBudget layout.powers mulTime degree + 200 * layout.width)
    (Powers.codeBudget layout.powers mulWords degree + 600 * layout.width + 200) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _
    (generated_bounded layout mul mulBuffers reserve budget)
    (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals
    have parts := layout.parts
    dsimp only [Layouts.input, Layout.prod, Representation.transport, Representation.prod,
      Encoding.transport, Encoding.prod, Encoding.checked] at parts ⊢
    omega

def timeBudget (mulTime : Nat) : Nat := Powers.timeBudget layout.powers mulTime degree + 216 * layout.width
def codeBudget (mulWords : Nat) : Nat := Powers.codeBudget layout.powers mulWords degree + 700 * layout.width + 300

include budget in
theorem bounded : (implementation layout oneValid mul mulBuffers reserve).BoundedBy
    (timeBudget layout mulTime) (codeBudget layout mulWords) := by
  apply ((prepare_bounded layout mul mulBuffers reserve budget).then
    (ProximityTerms.bounded layout.terms oneValid)).mono
  all_goals
    have := layout.parts
    dsimp only [timeBudget, codeBudget, ProximityTerms.timeBudget, ProximityTerms.codeBudget]
    omega

theorem names {names : Nat} (named : NamesAccounted mul.program.code names) :
    NamesAccounted (implementation layout oneValid mul mulBuffers reserve).program.code names := by
  have generatedNames : NamesAccounted (generated layout mul mulBuffers reserve).program.code names :=
    ((Implementation.first_names _ _ _ _ _).seq (duplicate_names layout names)).seq
      (Powers.names layout.powers reserve mul mulBuffers named degree (Nat.le_refl _))
  have prepared : NamesAccounted (prepare layout mul mulBuffers reserve).program.code names :=
    Implementation.pair_names _ _ _ _ _ _ _ _ generatedNames (Implementation.second_names _ _ _ _ _)
  exact prepared.seq (ProximityTerms.names layout.terms oneValid names)

include budget in
theorem resources {names : Nat} (named : NamesAccounted mul.program.code names)
    (tape : RandomTape w) (input : layout.input.Value) (before : State w)
    (holds : layout.input.representation.Holds input before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout oneValid mul mulBuffers reserve).program.code before after
      ((implementation layout oneValid mul mulBuffers reserve).program.time input) net peak ∧
      layout.output.representation.Holds
        ⟨value input.val, (implementation layout oneValid mul mulBuffers reserve).preserves input.val input.property⟩ after ∧
      (implementation layout oneValid mul mulBuffers reserve).program.time input ≤ timeBudget layout mulTime ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout oneValid mul mulBuffers reserve).program.code before between ∨ between = after) →
        (staticWords (implementation layout oneValid mul mulBuffers reserve).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout oneValid mul mulBuffers reserve).program.code.memBound) ≤
            5 * codeBudget layout mulWords + 4 * names + registers + 3 * buffers + before.liveMem buffers + timeBudget layout mulTime := by
  obtain ⟨after, net, peak, execution, output, elapsed, memory⟩ :=
    (bounded layout oneValid mul mulBuffers reserve budget).memoryBound
      (OOPSTerms.names layout oneValid mul mulBuffers reserve named) tape input before holds
      registers buffers initialRegisters initialBuffers
  exact ⟨after, net, peak, execution, output, elapsed, fun between visited => (memory between visited).2.2.2⟩

end Signatures.Runtime.CaliperBackend.OOPSTerms
