import Signatures.Runtime.Caliper.SchnorrAGMSampled

/-! Whole-program bounds for sampled Schnorr signing. Composition executes
the three proved stages and adds only the two stored sequencing nodes. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Sampled
open Caliper BoundedSource
variable {w qH qS : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [Neg F]
    [DecidableEq M] [DecidableEq G] (layout : Histories.Layouts w M F G qH qS)

def timeBudget (scaleTime subTime negateTime : Nat) : Nat :=
  Arithmetic.timeBudget layout.signing scaleTime subTime negateTime + Histories.timeBudget layout + Programming.timeBudget layout
def codeBudget (scaleWords subWords negateWords : Nat) : Nat :=
  Arithmetic.codeBudget layout.signing scaleWords subWords negateWords + Histories.codeBudget layout + Programming.codeBudget layout + 2

variable (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.signing.arithmetic.scaleArgs layout.scheme.point (fun args => args.1 • args.2))
    (sub : Implementation .unit layout.signing.arithmetic.points layout.scheme.point (fun args => args.1 - args.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

theorem bounded {scaleTime scaleWords subTime subWords negateTime negateWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (negateBound : negate.BoundedBy negateTime negateWords) :
    (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).BoundedBy
      (timeBudget layout scaleTime subTime negateTime) (codeBudget layout scaleWords subWords negateWords) := by
  have arithmeticBound : (arithmetic layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).BoundedBy
      (Arithmetic.timeBudget layout.signing scaleTime subTime negateTime) (Arithmetic.codeBudget layout.signing scaleWords subWords negateWords) :=
    (((Arithmetic.bounded layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve
      scaleBound subBound negateBound).restrictInput (admissible layout)).restrictOutput layout.room _).restrictOutput (cacheRoom layout) _
  have historyBound : (histories layout).BoundedBy (Histories.timeBudget layout) (Histories.codeBudget layout) :=
    ((Histories.bounded layout).restrictInput (cacheRoom layout)).restrictOutput _ _
  apply (((arithmeticBound.then historyBound).then (Programming.bounded layout)).castFunction rfl).mono
  · rfl
  · unfold codeBudget; omega

theorem static_bound {scaleTime scaleWords subTime subWords negateTime negateWords named : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (negateBound : negate.BoundedBy negateTime negateWords)
    (scaleNames : NamesAccounted scale.program.code named) (subNames : NamesAccounted sub.program.code named)
    (negateNames : NamesAccounted negate.program.code named) (registers buffers : Nat) :
    staticWords (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code registers buffers ≤
      5 * codeBudget layout scaleWords subWords negateWords + 4 * max 5 named + registers + 3 * buffers := by
  have stored := (bounded layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve scaleBound subBound negateBound).code_le
  have accounted := names layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve scaleNames subNames negateNames
  have registerBound := accounted.registers
  have bufferBound := accounted.buffers
  unfold staticWords
  omega

theorem resources {scaleTime scaleWords subTime subWords negateTime negateWords named : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (negateBound : negate.BoundedBy negateTime negateWords)
    (scaleNames : NamesAccounted scale.program.code named) (subNames : NamesAccounted sub.program.code named)
    (negateNames : NamesAccounted negate.program.code named)
    (tape : RandomTape w) (args : (input layout).Value) (before : State w)
    (holds : (input layout).representation.Holds args before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code
      before after ((implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.time args) net peak ∧
      (Programming.output layout).representation.Holds
        ⟨value args.val, (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).preserves args.val args.property⟩ after ∧
      (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.time args ≤ timeBudget layout scaleTime subTime negateTime ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code
          before between ∨ between = after) →
        (staticWords (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code.memBound) ≤
          5 * codeBudget layout scaleWords subWords negateWords + 4 * max 5 named + registers + 3 * buffers + before.liveMem buffers +
            timeBudget layout scaleTime subTime negateTime := by
  obtain ⟨after, net, peak, execution, result, elapsed, _, _⟩ :=
    (bounded layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve scaleBound subBound negateBound).exec (by decide) tape args before holds
  refine ⟨after, net, peak, execution, result, elapsed, ?_⟩
  intro between visited
  have memory := (LocalReach.total_memory_bound execution visited registers buffers initialRegisters initialBuffers holds.2.2.1).2.2.2
  have stored := static_bound layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve
    scaleBound subBound negateBound scaleNames subNames negateNames registers buffers
  omega

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Sampled
