import Proofs.Runtime.Caliper.SchnorrAGMFlattenLayout

/-! One executed affine update. Routing physically rearranges the current
basis element, coefficient and accumulator for the existing two-coordinate
scalar arithmetic routine. Only multiplication and addition are supplied. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Flatten
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

def routeValue (value : layout.body.Value) : layout.affine.Value × (layout.scalar.Value × layout.affine.Value) :=
  (⟨value.val.1.1, value.property.1.1⟩, ⟨value.val.1.2, value.property.1.2⟩,
    ⟨value.val.2.1, value.property.2.1⟩)

def route : Implementation .unit layout.body layout.arithmetic.bad (fun value => (value.1.2, value.1.1, value.2.1)) where
  preserves _ valid := ⟨valid.1.2, valid.1.1, valid.2.1⟩
  program := ((Reorder.realizer .unit (by decide) layout.affine.representation layout.scalar.representation
    layout.affine.representation layout.wordFits (by
      have := layout.argFits
      change (layout.affine.representation.encoding.words + layout.scalar.representation.encoding.words) +
        layout.affine.representation.encoding.words + 0 < _ at this
      omega)).viewInput layout.body.representation (routeValue layout) (by
        intro value
        change (_ ++ _) ++ (_ ++ []) = _ ++ (_ ++ _)
        simp only [List.append_nil, List.append_assoc]
        rfl)).viewOutput layout.arithmetic.bad.representation _ (fun _ => rfl)

theorem route_buffers : (route layout).program.code.memBound ≤ 2 := Reorder.buffers _ _ _
theorem route_bounded : (route layout).BoundedBy (40 * layout.scalar.representation.encoding.words)
    (130 * layout.scalar.representation.encoding.words + 14) := by
  constructor
  · intro value
    have bound := Reorder.time_unit_le (w := w) layout.affine.representation.encoding.words
      layout.scalar.representation.encoding.words layout.affine.representation.encoding.words
    exact bound.trans (by rw [Layouts.affine_words]; omega)
  · have bound := Reorder.descriptionWords_le (w := w) layout.affine.representation.encoding.words
      layout.scalar.representation.encoding.words layout.affine.representation.encoding.words
    exact bound.trans (by rw [Layouts.affine_words]; omega)

def step [Mul F] [Add F] (value : ((F × F) × F) × ((F × F) × Unit)) : F × F :=
  (value.2.1.1 + value.1.2 * value.1.1.1, value.2.1.2 + value.1.2 * value.1.1.2)

variable [Mul F] [Add F]
    (mul : Implementation .unit layout.affine layout.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

def body : Implementation .unit layout.body layout.affine step :=
  ((route layout).then (BLSAccumulate.bad layout.arithmetic mul add mulBuffers reserve addBuffers)).castFunction (by
    funext value
    rfl)

theorem body_buffers : (body layout mul add mulBuffers addBuffers reserve).program.code.memBound ≤ max 3 slots + 2 :=
  max_le ((route_buffers layout).trans (by omega))
    (BLSAccumulate.bad_buffers layout.arithmetic mul add mulBuffers reserve addBuffers)

def bodyTime (mulTime addTime : Nat) : Nat :=
  2 * mulTime + 2 * addTime + 2816 * layout.scalar.representation.encoding.words
def bodyWords (mulWords addWords : Nat) : Nat :=
  2 * mulWords + 2 * addWords + 9152 * layout.scalar.representation.encoding.words + 1485

theorem body_bounded {mulTime mulWords addTime addWords : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords) :
    (body layout mul add mulBuffers addBuffers reserve).BoundedBy
      (bodyTime layout mulTime addTime) (bodyWords layout mulWords addWords) := by
  have combined := (route_bounded layout).then
    (BLSAccumulate.bad_bounded layout.arithmetic mul add mulBound addBound mulBuffers reserve addBuffers)
  constructor
  · intro value
    exact (combined.time_le value).trans (by dsimp only [bodyTime, BLSAccumulate.badTime, Layouts.arithmetic]; omega)
  · exact combined.code_le.trans (by dsimp only [bodyWords, BLSAccumulate.badCode, Layouts.arithmetic]; omega)

theorem body_names (names : Nat) (mulNames : NamesAccounted mul.program.code names) (addNames : NamesAccounted add.program.code names) :
    NamesAccounted (body layout mul add mulBuffers addBuffers reserve).program.code names :=
  (Reorder.names _ _ _ names).seq
    (BLSAccumulate.bad_names layout.arithmetic names mul add mulNames addNames mulBuffers reserve addBuffers)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Flatten
