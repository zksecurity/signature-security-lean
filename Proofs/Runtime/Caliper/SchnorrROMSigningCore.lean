import Proofs.Runtime.Caliper.SchnorrROMSigningCache
import Proofs.Runtime.Caliper.ImplementationMemory

/-! Executed signing after its two private draws: compute the commitment,
program the managed cache, and return the signature and public configuration.
Only scalar multiplication and subtraction are supplied as local routines. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Core
open Caliper BoundedSource
variable {w : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (layout : Layouts w M F G) (zeroValid : layout.scalar.valid 0)
    (scale : Implementation .unit layout.arithmetic.scaleArgs layout.point (fun value => value.1 • value.2))
    (sub : Implementation .unit layout.arithmetic.points layout.point (fun value => value.1 - value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w)

def value (input : Input M F G) : Output M F G :=
  ((Arithmetic.commitment input, input.1.2), (input.2.1, input.2.2.1),
    Cache.update ((input.2.2.2.1, Arithmetic.commitment input), input.1.1, input.2.2.2.2, ()))
def implementation : Implementation .unit layout.input layout.output value :=
  ((Arithmetic.implementation layout zeroValid scale sub scaleBuffers subBuffers reserve).then (Cache.implementation layout)).castFunction rfl

def timeBudget (scaleTime subTime : Nat) := Arithmetic.timeBudget layout scaleTime subTime + Cache.timeBudget layout
def codeBudget (scaleWords subWords : Nat) := Arithmetic.codeBudget layout scaleWords subWords + Cache.codeBudget layout + 1

theorem bounded {scaleTime subTime scaleWords subWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords) :
    (implementation layout zeroValid scale sub scaleBuffers subBuffers reserve).BoundedBy
      (timeBudget layout scaleTime subTime) (codeBudget layout scaleWords subWords) :=
  ((Arithmetic.bounded layout zeroValid scale sub scaleBuffers subBuffers reserve scaleBound subBound).then
    (Cache.bounded layout)).castFunction rfl

theorem buffers : (implementation layout zeroValid scale sub scaleBuffers subBuffers reserve).program.code.memBound ≤ max 9 (slots + 2) := by
  have computed := Arithmetic.buffers layout zeroValid scale sub scaleBuffers subBuffers reserve
  have programmed := Cache.buffers layout
  change max _ _ ≤ _
  omega

theorem names (slotsNamed : Nat) (scaleNames : NamesAccounted scale.program.code slotsNamed)
    (subNames : NamesAccounted sub.program.code slotsNamed) :
    NamesAccounted (implementation layout zeroValid scale sub scaleBuffers subBuffers reserve).program.code (max 5 slotsNamed) :=
  ((Arithmetic.names layout zeroValid scale sub scaleBuffers subBuffers reserve slotsNamed scaleNames subNames).mono (Nat.le_max_right _ _)).seq
    ((Cache.names layout).mono (Nat.le_max_left _ _))

theorem resources {scaleTime subTime scaleWords subWords slotsNamed : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (scaleNames : NamesAccounted scale.program.code slotsNamed) (subNames : NamesAccounted sub.program.code slotsNamed)
    (tape : RandomTape w) (input : layout.input.Value) (before : State w)
    (holds : layout.input.representation.Holds input before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout zeroValid scale sub scaleBuffers subBuffers reserve).program.code before after
        ((implementation layout zeroValid scale sub scaleBuffers subBuffers reserve).program.time input) net peak ∧
      layout.output.representation.Holds
        ⟨value input.val, (implementation layout zeroValid scale sub scaleBuffers subBuffers reserve).preserves input.val input.property⟩ after ∧
      (implementation layout zeroValid scale sub scaleBuffers subBuffers reserve).program.time input ≤ timeBudget layout scaleTime subTime ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout zeroValid scale sub scaleBuffers subBuffers reserve).program.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots (implementation layout zeroValid scale sub scaleBuffers subBuffers reserve).program.code)) ∧
        between.SupportBound (max buffers (implementation layout zeroValid scale sub scaleBuffers subBuffers reserve).program.code.memBound) ∧ between.WellFormed ∧
        (staticWords (implementation layout zeroValid scale sub scaleBuffers subBuffers reserve).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout zeroValid scale sub scaleBuffers subBuffers reserve).program.code.memBound) ≤
            5 * codeBudget layout scaleWords subWords + 4 * max 5 slotsNamed + registers + 3 * buffers +
              before.liveMem buffers + timeBudget layout scaleTime subTime :=
  (bounded layout zeroValid scale sub scaleBuffers subBuffers reserve scaleBound subBound).memoryBound
    (names layout zeroValid scale sub scaleBuffers subBuffers reserve slotsNamed scaleNames subNames)
    tape input before holds registers buffers initialRegisters initialBuffers

omit [Zero F] in
theorem length (input : Input M F G) : (value input).2.2.length ≤ input.2.2.2.2.length + 1 :=
  Cache.length _

end Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Core
