import Signatures.Runtime.Caliper.SchnorrAGMFlatten

/-! Full flattening budgets derived from scalar multiplication and addition.
They include coefficient lookup, positional attachment, reversal, zero constants,
all copied frames, every stored fold branch and initial caller memory. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Flatten
open Caliper BoundedSource
variable {w : Nat} {F : Type} [Zero F] [Mul F] [Add F]
    (layout : Layouts w F) (zeroValid : layout.scalar.valid 0)
    (mul : Implementation .unit layout.affine layout.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

def foldWidth : Nat := ListFold.width layout.attach.row.representation.encoding.words
  layout.affine.representation.encoding.words layout.unit.representation.encoding.words layout.capacity
def foldTime (mulTime addTime : Nat) : Nat := 8 * layout.affine.representation.encoding.words +
  layout.capacity * (bodyTime layout mulTime addTime + 44 * foldWidth layout + 7)
def foldWords (mulWords addWords : Nat) : Nat := 26 * layout.affine.representation.encoding.words + 14 +
  layout.capacity * (bodyWords layout mulWords addWords + 169 * foldWidth layout + 115)

def timeBudget (mulTime addTime : Nat) : Nat :=
  24 * layout.width + AttachRows.timeBudget layout.attach + foldTime layout mulTime addTime
def codeBudget (mulWords addWords : Nat) : Nat :=
  78 * layout.width + AttachRows.codeBudget layout.attach + foldWords layout mulWords addWords + 31

omit [Zero F] in
theorem fold_bounded {mulTime mulWords addTime addWords : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords) :
    (fold layout mul add mulBuffers addBuffers reserve).BoundedBy
      (foldTime layout mulTime addTime) (foldWords layout mulWords addWords) :=
  FoldImplementation.compile_boundedBy layout.attach.row layout.affine layout.unit layout.argFits
    (body layout mul add mulBuffers addBuffers reserve) layout.wordFits (body_nameFits layout mul add mulBuffers addBuffers reserve)
    layout.capacity layout.attach.countFits layout.foldFits _ _
    (body_bounded layout mul add mulBuffers addBuffers reserve mulBound addBound)

theorem bounded {mulTime mulWords addTime addWords : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords) :
    (implementation layout zeroValid mul add mulBuffers addBuffers reserve).BoundedBy
      (timeBudget layout mulTime addTime) (codeBudget layout mulWords addWords) := by
  have combined := (((prepare_bounded layout zeroValid).then (AttachRows.bounded layout.attach)).then
    (initial_bounded layout zeroValid)).then (fold_bounded layout mul add mulBuffers addBuffers reserve mulBound addBound)
  have widths := layout.sizes
  constructor
  · intro value
    exact (combined.time_le value).trans (by unfold timeBudget; omega)
  · exact combined.code_le.trans (by unfold codeBudget; omega)

theorem static_bound {mulTime mulWords addTime addWords names : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (mulNames : NamesAccounted mul.program.code names) (addNames : NamesAccounted add.program.code names)
    (registers buffers : Nat) :
    staticWords (implementation layout zeroValid mul add mulBuffers addBuffers reserve).program.code registers buffers ≤
      5 * codeBudget layout mulWords addWords + 4 * names + registers + 3 * buffers := by
  have stored := (bounded layout zeroValid mul add mulBuffers addBuffers reserve mulBound addBound).code_le
  have named := Flatten.names layout zeroValid mul add mulBuffers addBuffers reserve names mulNames addNames
  have registersBound := named.registers
  have buffersBound := named.buffers
  unfold staticWords
  omega

theorem resources {mulTime mulWords addTime addWords names : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (mulNames : NamesAccounted mul.program.code names) (addNames : NamesAccounted add.program.code names)
    (tape : RandomTape w) (value : layout.input.Value) (before : State w) (holds : layout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout zeroValid mul add mulBuffers addBuffers reserve).program.code before after
      ((implementation layout zeroValid mul add mulBuffers addBuffers reserve).program.time value) net peak ∧
      layout.affine.representation.Holds
        ⟨denote value.val, (implementation layout zeroValid mul add mulBuffers addBuffers reserve).preserves value.val value.property⟩ after ∧
      (implementation layout zeroValid mul add mulBuffers addBuffers reserve).program.time value ≤ timeBudget layout mulTime addTime ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout zeroValid mul add mulBuffers addBuffers reserve).program.code before between ∨ between = after) →
        (staticWords (implementation layout zeroValid mul add mulBuffers addBuffers reserve).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout zeroValid mul add mulBuffers addBuffers reserve).program.code.memBound) ≤
          5 * codeBudget layout mulWords addWords + 4 * names + registers + 3 * buffers + before.liveMem buffers + timeBudget layout mulTime addTime := by
  obtain ⟨after, net, peak, execution, output, elapsed, _, _⟩ :=
    (bounded layout zeroValid mul add mulBuffers addBuffers reserve mulBound addBound).exec (by decide) tape value before holds
  refine ⟨after, net, peak, execution, output, elapsed, ?_⟩
  intro between visited
  have memory := (LocalReach.total_memory_bound execution visited registers buffers initialRegisters initialBuffers holds.2.2.1).2.2.2
  have stored := static_bound layout zeroValid mul add mulBuffers addBuffers reserve mulBound addBound mulNames addNames registers buffers
  omega

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Flatten
