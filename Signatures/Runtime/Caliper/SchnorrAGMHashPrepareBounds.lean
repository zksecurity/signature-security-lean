import Signatures.Runtime.Caliper.SchnorrAGMHash

/-! The hash preparation overhead includes all retained original input words,
coefficient/basis copies, affine arithmetic and routing into the read frame. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Hash
open Caliper BoundedSource Assembly
variable {w qH qS : Nat} {M F G : Type} [Zero F] [Mul F] [Add F] [DecidableEq M] [DecidableEq G]
    (layout : Layouts w M F G qH qS) (zeroValid : layout.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

def prepareTime (mulTime addTime : Nat) : Nat := Flatten.timeBudget layout.flat mulTime addTime + 80 * layout.width
def prepareWords (mulWords addWords : Nat) : Nat := Flatten.codeBudget layout.flat mulWords addWords + 250 * layout.width + 70

private theorem then_time {A B C : Type} {input : Representation w A} {middle : Representation w B}
    {output : Representation w C} {f : A → B} {g : B → C}
    (first : Realizer .unit input middle f) (second : Realizer .unit middle output g)
    {firstTime secondTime : Nat} (firstBound : ∀ value, first.time value ≤ firstTime)
    (secondBound : ∀ value, second.time value ≤ secondTime) (value : A) :
    (first.then second).time value ≤ firstTime + secondTime :=
  Nat.add_le_add (firstBound value) (secondBound (f value))

theorem holdFlatten_time {mulTime mulWords addTime addWords : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords) (value : layout.Packed) :
    (holdFlatten layout zeroValid mul add mulBuffers addBuffers reserve).time value ≤
      Flatten.timeBudget layout.flat mulTime addTime + 8 * layout.flat.input.representation.encoding.words +
        8 * layout.flat.affine.representation.encoding.words + 12 * layout.input.representation.encoding.words := by
  have retained := (Flatten.implementation layout.flat zeroValid mul add mulBuffers addBuffers reserve).program.retain_time_unit_le
    layout.input.representation layout.scheme.wordFits (flatten_nameFits layout zeroValid mul add mulBuffers addBuffers reserve)
    layout.packed.fits layout.flattened.fits value
  have computed := (Flatten.bounded layout.flat zeroValid mul add mulBuffers addBuffers reserve mulBound addBound).time_le value.1
  exact retained.trans (by omega)

theorem prepare_time {mulTime mulWords addTime addWords : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords) (value : layout.input.Value) :
    (prepare layout zeroValid mul add mulBuffers addBuffers reserve).time value ≤ prepareTime layout mulTime addTime := by
  have packed : ∀ value, (pack layout).time value ≤ 8 * layout.packed.encoding.words := by
    intro value
    have bound := code_time_unit_le (packOperands layout)
    rw [packOperands_length] at bound
    exact bound
  have finished : ∀ value, (finish layout).time value ≤ 8 * (Read.input layout.scheme).representation.encoding.words := by
    intro value
    have bound := code_time_unit_le (finishOperands layout)
    rw [finishOperands_length] at bound
    exact bound
  have combined := then_time ((pack layout).then (holdFlatten layout zeroValid mul add mulBuffers addBuffers reserve)) (finish layout)
    (then_time (pack layout) (holdFlatten layout zeroValid mul add mulBuffers addBuffers reserve)
      packed (holdFlatten_time layout zeroValid mul add mulBuffers addBuffers reserve mulBound addBound)) finished value
  have frames := layout.sizes
  have flatFrames := layout.flat.sizes
  have readFrames := Read.sizes layout.scheme
  have base := layout.flat.attach.base_sizes
  rw [Flatten.Layouts.attach_width] at base
  have affine : layout.flat.affine.representation.encoding.words ≤ layout.flat.width := base.1
  have widths := layout.width_eq
  exact combined.trans (by unfold prepareTime; omega)

theorem prepare_words {mulTime mulWords addTime addWords : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords) :
    descriptionWords (prepare layout zeroValid mul add mulBuffers addBuffers reserve).code ≤ prepareWords layout mulWords addWords := by
  have packed := code_descriptionWords_le (packOperands layout)
  rw [packOperands_length] at packed
  have held := (Flatten.implementation layout.flat zeroValid mul add mulBuffers addBuffers reserve).program.retain_descriptionWords_le
    (by decide) layout.input.representation layout.scheme.wordFits (flatten_nameFits layout zeroValid mul add mulBuffers addBuffers reserve)
    layout.packed.fits layout.flattened.fits
  have flattened := (Flatten.bounded layout.flat zeroValid mul add mulBuffers addBuffers reserve mulBound addBound).code_le
  have finished := code_descriptionWords_le (finishOperands layout)
  rw [finishOperands_length] at finished
  change descriptionWords (pack layout).code ≤ _ at packed
  change descriptionWords (holdFlatten layout zeroValid mul add mulBuffers addBuffers reserve).code ≤ _ at held
  change descriptionWords (finish layout).code ≤ _ at finished
  change descriptionWords (((pack layout).code ;; (holdFlatten layout zeroValid mul add mulBuffers addBuffers reserve).code) ;; (finish layout).code) ≤ _
  rw [descriptionWords_seq, descriptionWords_seq]
  have frames := layout.sizes
  have flatFrames := layout.flat.sizes
  have readFrames := Read.sizes layout.scheme
  have base := layout.flat.attach.base_sizes
  rw [Flatten.Layouts.attach_width] at base
  have affine : layout.flat.affine.representation.encoding.words ≤ layout.flat.width := base.1
  have widths := layout.width_eq
  unfold prepareWords
  omega

theorem prepare_names (names : Nat) (mulNames : NamesAccounted mul.program.code names) (addNames : NamesAccounted add.program.code names) :
    NamesAccounted (prepare layout zeroValid mul add mulBuffers addBuffers reserve).code names :=
  ((code_namesAccounted _ _ (packOperands_sources layout)).seq
    (Retain.names (Flatten.names layout.flat zeroValid mul add mulBuffers addBuffers reserve names mulNames addNames) _ _ _)).seq
      (code_namesAccounted _ _ (finishOperands_sources layout))

theorem prepare_buffers : (prepare layout zeroValid mul add mulBuffers addBuffers reserve).code.memBound ≤ max 11 (max 3 slots + 4) := by
  have packed := (code_names _ 1 (packOperands_sources layout)).2
  have finished := (code_names _ 1 (finishOperands_sources layout)).2
  have flattened := Flatten.buffers layout.flat zeroValid mul add mulBuffers addBuffers reserve
  have held := (Retain.code_names (Flatten.implementation layout.flat zeroValid mul add mulBuffers addBuffers reserve).program.code
    (max 2 (Flatten.implementation layout.flat zeroValid mul add mulBuffers addBuffers reserve).program.code.memBound)
    layout.flat.input.representation.encoding.words layout.flat.affine.representation.encoding.words layout.input.representation.encoding.words
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)).2
  change (pack layout).code.memBound ≤ 2 at packed
  change (finish layout).code.memBound ≤ 2 at finished
  change (holdFlatten layout zeroValid mul add mulBuffers addBuffers reserve).code.memBound ≤ _ at held
  change max (max (pack layout).code.memBound (holdFlatten layout zeroValid mul add mulBuffers addBuffers reserve).code.memBound)
    (finish layout).code.memBound ≤ _
  omega

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Hash
