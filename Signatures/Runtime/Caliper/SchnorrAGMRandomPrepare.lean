import Signatures.Runtime.Caliper.SchnorrAGMRandomMark

/-! Executed random-request preparation tests the group-list length, drops
the represented lists, and marks malformed only on the nonempty branch. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
open Caliper BoundedSource
variable {w qH qS randomBound : Nat} {M F G : Type} (layout : Layouts w M F G qH qS randomBound)

def project : Implementation .unit layout.input layout.base (fun args => args.2.2) :=
  (Implementation.second (by decide) layout.points layout.tail layout.scheme.wordFits layout.input.representation.fits).then
    (Implementation.second (by decide) layout.coefficientRows layout.base layout.scheme.wordFits layout.tail.representation.fits)
theorem project_bounded : (project layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  have bound := (Implementation.second_boundedBy layout.points layout.tail layout.scheme.wordFits layout.input.representation.fits).then
    (Implementation.second_boundedBy layout.coefficientRows layout.base layout.scheme.wordFits layout.tail.representation.fits)
  apply bound.mono
  all_goals
    have base := layout.base_le
    have small : layout.tail.representation.encoding.words ≤ layout.width := by
      have input := layout.input_le
      change layout.points.representation.encoding.words + layout.tail.representation.encoding.words ≤ _ at input
      omega
    omega
theorem project_names (slots : Nat) : NamesAccounted (project layout).program.code slots :=
  (Implementation.second_names layout.points layout.tail layout.scheme.wordFits layout.input.representation.fits slots).seq
    (Implementation.second_names layout.coefficientRows layout.base layout.scheme.wordFits layout.tail.representation.fits slots)
theorem project_buffers : (project layout).program.code.memBound ≤ 2 :=
  max_le (Implementation.second_buffers (cost := .unit) (by decide) layout.points layout.tail layout.scheme.wordFits layout.input.representation.fits)
    (Implementation.second_buffers (cost := .unit) (by decide) layout.coefficientRows layout.base layout.scheme.wordFits layout.tail.representation.fits)

def accepted := (project layout).restrictInput (fun args => shape args = true)
def rejected := ((project layout).then (mark layout)).restrictInput (fun args => shape args = false)
theorem prepare_source : (fun args : Input M F G => if shape args = true then args.2.2 else markValue args.2.2) =
    Signatures.Runtime.SchnorrAGM.Native.Random.prepareValue := by
  funext args
  rcases args with ⟨groups, rows, n, state⟩
  cases groups <;> rfl
def prepare : Implementation .unit layout.input layout.base Signatures.Runtime.SchnorrAGM.Native.Random.prepareValue :=
  (GuardedBranch.implementation (hw := layout.scheme.wordFits) (test layout) (by decide)
    (test_nameFits layout) layout.duplicateFits layout.tagFits (accepted layout) (rejected layout)).castFunction prepare_source
theorem prepare_bounded : (prepare layout).BoundedBy (128 * layout.width + 128) (512 * layout.width + 600) := by
  have acceptedBound := (project_bounded layout).restrictInput (fun args => shape args = true)
  have rejectedBound := ((project_bounded layout).then (mark_bounded layout)).restrictInput (fun args => shape args = false)
  have bound := GuardedBranch.implementation_boundedBy (hw := layout.scheme.wordFits) (test layout) (test_nameFits layout) layout.duplicateFits layout.tagFits
    (accepted layout) (rejected layout) (test_bounded layout) acceptedBound rejectedBound
  apply (bound.castFunction prepare_source).mono <;> have := layout.input_le <;> omega
theorem prepare_names : NamesAccounted (prepare layout).program.code 5 :=
  GuardedBranch.implementation_names (test layout) (test_nameFits layout) layout.duplicateFits layout.tagFits
    (accepted layout) (rejected layout) (test_names layout).accounted (project_names layout 5)
      ((project_names layout 5).seq (mark_names layout 5))
theorem prepare_buffers : (prepare layout).program.code.memBound ≤ 6 :=
  GuardedBranch.implementation_buffers (test layout) (test_nameFits layout) layout.duplicateFits layout.tagFits
    (accepted layout) (rejected layout) (test_names layout).buffers (project_buffers layout)
      (max_le (project_buffers layout) ((mark_buffers layout).trans (by decide)))

def preparedValue (args : layout.input.Value) : Fin (randomBound + 1) × layout.scheme.state.Value :=
  let result : layout.base.Value := ⟨Signatures.Runtime.SchnorrAGM.Native.Random.prepareValue args.val,
    (prepare layout).preserves args.val args.property⟩
  (⟨result.val.1, result.property.1⟩, ⟨result.val.2, result.property.2⟩)
def prepareQuery : Realizer .unit layout.input.representation
    (UniformQuery.input randomBound layout.scheme.wordFits layout.rangeFits layout.scheme.state.representation layout.frameFits)
    (preparedValue layout) :=
  (prepare layout).program.viewOutput _ (preparedValue layout) (fun _ => rfl)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
