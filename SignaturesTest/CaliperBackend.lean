import Proofs.Runtime.Caliper
import Lean

open Caliper Signatures.Runtime.CaliperBackend

namespace SignaturesTest.CaliperBackend

private def representation := wordRepresentation 8 (by decide)
private def initial : State 8 := representation.initial 42

-- Actual memory-load / bit-complement / memory-store execution, with exact cost.
example : (Caliper.run .unit RandomTape.zero 10 (complementCode 8) initial).map
    (fun (state, time, net, peak) => (state.bufs 0, time, net, peak)) =
    some (#[213], 3, 0, 0) := by decide

-- Composition is literal machine-code sequencing. Both calls are charged.
example : (Caliper.run .unit RandomTape.zero 20
    ((complementRealizer .unit).then (complementRealizer .unit)).code initial).map
    (fun (state, time, net, peak) => (state.bufs 0, time, net, peak)) =
    some (#[42], 6, 0, 0) := by decide

example : (quantitative 8 (by decide) .unit).cost (complementRealizer .unit) 42 = 3 := rfl
example : (quantitative 8 (by decide) .unit).cost
    ((complementRealizer .unit).then (complementRealizer .unit)) 42 = 6 := rfl

-- Macro calls use the selected Caliper implementation and charge its full body.
private def library : Library 8 Unit := fun _ => complementCode 8
private def hybrid : Program 8 Unit := .seq (.call ()) (.call ())
example : (hybrid.run .unit RandomTape.zero library 20 initial).map
    (fun (state, time, net, peak) => (state.bufs 0, time, net, peak)) =
    some (#[42], 6, 0, 0) := by decide
example : hybrid.descriptionWords library = 29 := by decide
example : (descriptionSizes 8 (by decide) .unit).localSize (complementRealizer .unit) = 14 := rfl

-- Descriptor, register and stored-program reservations are separate from buffer memory.
example : staticWords (complementCode 8) 1 1 = 19 := by decide

-- An out-of-range address is rejected, not interpreted as a free read of zero.
example : (Caliper.run .unit RandomTape.zero 10 (complementCode 8)
    (initial.setReg 0 1)).isNone = true := by decide
example : (Caliper.run .unit RandomTape.zero 0 (complementCode 8) initial).isNone = true := rfl

-- Immediates and static names exceeding the word width fail the description contract.
example : ¬ DescriptionFits (Stmt.memAllocI (w := 8) 0 256) := by
  simp [DescriptionFits, description]
example : ¬ DescriptionFits (Stmt.mov (w := 8) 256 0) := by
  simp [DescriptionFits, description]
example : ¬ Location.NamesFit 8 .scalar ⟨256, 0⟩ := by simp [Location.NamesFit]
example : ¬ Address.Valid ⟨0, 0⟩ 1 { initial with caps := fun _ => 256 } := by
  simp [Address.Valid]

-- The frame protects the next value even when both values share one arena.
private def representations : Representations 8 (Word 8) (Word 8) (Word 8) :=
  ⟨wordEncoding 8, wordEncoding 8, wordEncoding 8, by decide, by decide, by decide⟩
private def addCall : Call :=
  ⟨[.scalar, .scalar], .scalar, .add, (⟨0, 0⟩, ⟨0, 0⟩, ()), ⟨0, 0⟩⟩
private def sharedArena : State 8 :=
  { State.init 8 with
    bufs := fun b => if b = 0 then #[1, 2] else #[]
    caps := fun b => if b = 0 then 2 else 0 }
example : ¬ addCall.Frame representations ⟨∅, ∅⟩ sharedArena
    (sharedArena.setBuf 0 #[3, 9]) := by
  intro frame
  have protectedWord := frame.2.2.2.1 0 1 (by
    simp [Call.Writes, addCall, Address.start, sharedArena, State.init,
      Representations.words, representations, wordEncoding])
  have different : (9 : Word 8) ≠ 2 := by decide
  exact different (Option.some.inj protectedWord)

-- A clone pays for its copied payload and reserves a separate destination.
private def copyInitial : State 8 :=
  { State.init 8 with
    bufs := fun b => if b = 0 then #[7, 11, 13] else #[]
    caps := fun b => if b = 0 then 3 else 0 }
example : (Caliper.run .unit RandomTape.zero 100 (copyBuffer 0 1) copyInitial).map
    (fun (state, time, net, peak) =>
      (state.bufs 0, state.bufs 1, state.tapePos, time, net, peak)) =
    some (#[7, 11, 13], #[7, 11, 13], 0, 25, 3, 3) := by decide

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Realizer.execution_cost, ``Realizer.execution_bounds,
      ``Realizer.then_description, ``Realizer.total_memory_bound,
      ``complementRealizer, ``CertifiedLibrary.call_exec, ``CertifiedLibrary.call_triple,
      ``Signatures.Runtime.CaliperBackend.Triple.seq,
      ``Signatures.Runtime.CaliperBackend.Triple.branch,
      ``Signatures.Runtime.CaliperBackend.Triple.loop,
      ``copyBuffer_spec, ``copyBuffer_tape] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperBackend
