import Signatures.Runtime.Caliper.SchnorrAGMSigningArithmetic

/-! Derived whole-stage signing arithmetic budgets. The memory statement
covers the same source-correct execution, including its stored program,
initial caller state, retained input and all intermediate buffers. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Arithmetic
open Caliper BoundedSource Assembly
variable {w qH qS : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [Neg F]
    (layout : Layouts w M F G qH qS) (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.arithmetic.scaleArgs layout.scheme.point (fun value => value.1 • value.2))
    (sub : Implementation .unit layout.arithmetic.points layout.scheme.point (fun value => value.1 - value.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

def timeBudget (scaleTime subTime negateTime : Nat) : Nat := 2 * scaleTime + subTime + negateTime + 512 * layout.width
def codeBudget (scaleWords subWords negateWords : Nat) : Nat := 2 * scaleWords + subWords + negateWords + 2048 * layout.width + 1024

private theorem then_time {A B C : Type} {input : Representation w A} {middle : Representation w B}
    {output : Representation w C} {f : A → B} {g : B → C}
    (first : Realizer .unit input middle f) (second : Realizer .unit middle output g)
    {firstTime secondTime : Nat} (firstBound : ∀ input, first.time input ≤ firstTime)
    (secondBound : ∀ input, second.time input ≤ secondTime) (input : A) :
    (first.then second).time input ≤ firstTime + secondTime :=
  Nat.add_le_add (firstBound input) (secondBound (f input))

theorem bounded {scaleTime scaleWords subTime subWords negateTime negateWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (negateBound : negate.BoundedBy negateTime negateWords) :
    (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).BoundedBy
      (timeBudget layout scaleTime subTime negateTime) (codeBudget layout scaleWords subWords negateWords) := by
  have inputSize := layout.input_le
  have outputSize := layout.work_le
  have computedSize : layout.computed.representation.encoding.words ≤ layout.width := by
    change layout.scheme.point.representation.encoding.words + layout.scheme.scalar.representation.encoding.words ≤ _
    unfold Layouts.width; omega
  have body := computed_bounded layout zeroValid scale sub scaleBuffers reserve negate subBuffers negateBuffers
    scaleBound subBound negateBound
  constructor
  · intro input
    have duplicated : ∀ input, (duplicateRealizer .unit (by decide) layout.input.representation
        layout.scheme.wordFits layout.duplicated.fits).time input ≤ 16 * layout.input.representation.encoding.words := by
      intro input
      have bound := code_time_unit_le (reads (w := w) 0 0 layout.input.representation.encoding.words ++
        reads 0 0 layout.input.representation.encoding.words)
      simp only [List.length_append, reads_length] at bound
      exact bound.trans (by omega)
    have held : ∀ input, (retainComputed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).time input ≤
        computedTime layout scaleTime subTime negateTime + 20 * layout.input.representation.encoding.words +
          8 * layout.computed.representation.encoding.words := by
      intro input
      have bound := (computed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.retain_time_unit_le
        layout.input.representation layout.scheme.wordFits
        (computed_nameFits layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve)
        layout.duplicated.fits layout.frame.fits input
      have elapsed := body.time_le input.1
      exact bound.trans (by omega)
    have finished : ∀ input, (finish layout zeroValid).time input ≤ 8 * layout.work.representation.encoding.words := by
      intro input
      have bound := code_time_unit_le (finishOperands layout zeroValid)
      rw [finishOperands_length] at bound
      exact bound
    have combined := then_time
      ((duplicateRealizer .unit (by decide) layout.input.representation layout.scheme.wordFits layout.duplicated.fits).then
        (retainComputed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve)) (finish layout zeroValid)
      (then_time _ _ duplicated held) finished input
    exact combined.trans (by unfold timeBudget computedTime; omega)
  · have duplicated := code_descriptionWords_le (reads (w := w) 0 0 layout.input.representation.encoding.words ++
      reads 0 0 layout.input.representation.encoding.words)
    simp only [List.length_append, reads_length] at duplicated
    have held := (computed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.retain_descriptionWords_le
      (by decide) layout.input.representation layout.scheme.wordFits
      (computed_nameFits layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve)
      layout.duplicated.fits layout.frame.fits
    have finished := code_descriptionWords_le (finishOperands layout zeroValid)
    rw [finishOperands_length] at finished
    change descriptionWords (duplicateRealizer .unit (by decide) layout.input.representation layout.scheme.wordFits layout.duplicated.fits).code ≤ _ at duplicated
    change descriptionWords (retainComputed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).code ≤ _ at held
    change descriptionWords (finish layout zeroValid).code ≤ _ at finished
    change descriptionWords (((duplicateRealizer .unit (by decide) layout.input.representation layout.scheme.wordFits layout.duplicated.fits).code ;;
      (retainComputed layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).code) ;; (finish layout zeroValid).code) ≤ _
    rw [descriptionWords_seq, descriptionWords_seq]
    have stored := body.code_le
    unfold codeBudget computedWords at *
    omega

theorem static_bound {scaleTime scaleWords subTime subWords negateTime negateWords slotsNamed : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (negateBound : negate.BoundedBy negateTime negateWords)
    (scaleNames : NamesAccounted scale.program.code slotsNamed) (subNames : NamesAccounted sub.program.code slotsNamed)
    (negateNames : NamesAccounted negate.program.code slotsNamed) (registers buffers : Nat) :
    staticWords (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code registers buffers ≤
      5 * codeBudget layout scaleWords subWords negateWords + 4 * slotsNamed + registers + 3 * buffers := by
  have stored := (bounded layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve scaleBound subBound negateBound).code_le
  have named := names layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve slotsNamed scaleNames subNames negateNames
  have registersBound := named.registers
  have buffersBound := named.buffers
  unfold staticWords
  omega

theorem resources {scaleTime scaleWords subTime subWords negateTime negateWords slotsNamed : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (negateBound : negate.BoundedBy negateTime negateWords)
    (scaleNames : NamesAccounted scale.program.code slotsNamed) (subNames : NamesAccounted sub.program.code slotsNamed)
    (negateNames : NamesAccounted negate.program.code slotsNamed)
    (tape : RandomTape w) (input : layout.input.Value) (before : State w) (holds : layout.input.representation.Holds input before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code before after
      ((implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.time input) net peak ∧
      layout.work.representation.Holds
        ⟨value input.val, (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).preserves input.val input.property⟩ after ∧
      (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.time input ≤ timeBudget layout scaleTime subTime negateTime ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code before between ∨ between = after) →
        (staticWords (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code.memBound) ≤
          5 * codeBudget layout scaleWords subWords negateWords + 4 * slotsNamed + registers + 3 * buffers + before.liveMem buffers +
            timeBudget layout scaleTime subTime negateTime := by
  obtain ⟨after, net, peak, execution, output, elapsed, _, _⟩ :=
    (bounded layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve scaleBound subBound negateBound).exec (by decide) tape input before holds
  refine ⟨after, net, peak, execution, output, elapsed, ?_⟩
  intro between visited
  have memory := (LocalReach.total_memory_bound execution visited registers buffers initialRegisters initialBuffers holds.2.2.1).2.2.2
  have stored := static_bound layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve
    scaleBound subBound negateBound scaleNames subNames negateNames registers buffers
  omega

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Arithmetic
