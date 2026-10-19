import Signatures.Runtime.Caliper.SchnorrAGMSetup
import Signatures.Runtime.Caliper.SchnorrAGMReachability
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

namespace SignaturesTest.CaliperSchnorrAGMSetup

-- Word-level wiring fixture, with an infinite source message type. This is not
-- a cryptographic group implementation. Setup requires only represented 0/1.
private def layout : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Fin 4) (Word 16) 1 1 where
  scalar := Layout.all (Representation.fin 16 4 (by decide) (by decide))
  point := Layout.all (wordRepresentation 16 (by decide))
  message := Layout.counter 16 256 (by decide) (by decide)
  wordFits := by decide
  countFits := by decide
  storageFits := by decide

private def emptyLayout : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Fin 4) (Word 16) 0 0 where
  scalar := layout.scalar
  point := layout.point
  message := layout.message
  wordFits := by decide
  countFits := by decide
  storageFits := by decide

private def setup := CaliperBackend.SchnorrAGM.Setup.implementation layout trivial trivial

example : layout.state.representation.encoding.words = 30 := rfl
example : layout.initialized.representation.encoding.words = 34 := rfl
example : emptyLayout.state.representation.encoding.words = 15 := rfl
example : ¬ layout.message.valid 256 := Nat.lt_irrefl 256
example : ¬ layout.basis.valid [(0, 0), (0, 0), (0, 0), (0, 0)] :=
  fun admitted => (by decide : ¬ 4 ≤ 3) admitted.1
example : ¬ layout.signed.valid [1, 2] := fun admitted => (by decide : ¬ 2 ≤ 1) admitted.1
example : ¬ layout.cache.lookup.table.valid (List.replicate 4 ((1, 2), (0, false, 0, 0))) :=
  fun admitted => (by decide : ¬ 4 ≤ 3) admitted.1
example : ¬ layout.cache.lookup.table.valid [((256, 2), (0, false, 0, 0))] := by
  intro admitted
  exact Nat.lt_irrefl 256 (admitted.2 ((256, 2), (0, false, 0, 0)) (by simp)).1.1

private theorem bounded : setup.BoundedBy (8 * 34) (26 * 34 + 14) :=
  CaliperBackend.SchnorrAGM.Setup.bounded layout trivial trivial
private theorem names : NamesBound setup.program.code 3 :=
  CaliperBackend.SchnorrAGM.Setup.names layout trivial trivial

-- Total memory is bounded on the same execution that returns the initialized
-- bytes, including stored code, dense descriptors and retained input buffers.
private theorem memory (tape : RandomTape 16) (value : layout.config.Value) (before : State 16)
    (holds : layout.config.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape setup.program.code before after (setup.program.time value) net peak ∧
      layout.initialized.representation.Holds
        (CaliperBackend.SchnorrAGM.Setup.initialized layout trivial trivial value) after ∧
      setup.program.time value ≤ 8 * 34 ∧
      ∀ between, (Caliper.Reaches .unit tape setup.program.code before between ∨ between = after) →
        (staticWords setup.program.code registers buffers : Int) +
          between.liveMem (max buffers setup.program.code.memBound) ≤
            5 * (26 * 34 + 14) + 12 + registers + 3 * buffers + before.liveMem buffers + 8 * 34 := by
  obtain ⟨after, net, peak, execution, result, elapsed, states⟩ :=
    bounded.memoryBound names.accounted tape value before holds registers buffers initialRegisters initialBuffers
  exact ⟨after, net, peak, execution, result, elapsed, fun between visited => (states between visited).2.2.2⟩

private def execute {qH qS : Nat} (model : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Fin 4) (Word 16) qH qS)
    (zeroValid : model.scalar.valid 0) (oneValid : model.scalar.valid 1) (value : model.config.Value) :=
  let start := model.config.representation.initial value
  let before := { start with
    bufs := fun b => if b = 200 then #[77] else start.bufs b
    caps := fun b => if b = 200 then 4 else start.caps b
    regs := fun r => if r = 99 then 91 else start.regs r
    tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 10000
    (CaliperBackend.SchnorrAGM.Setup.implementation model zeroValid oneValid).program.code before).map fun result =>
      (result.1.bufs 0, result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
        result.1.caps 1, decide (result.2.1 ≤ 8 * model.initialized.representation.encoding.words))

open Lean in
run_cmd do
  let cache : Array (Word 16) := Array.replicate 19 0
  let basis : Array (Word 16) := #[2, 1, 0, 0, 1, 0, 0]
  let tail : Array (Word 16) := #[0, 0, 0, 0]
  unless execute layout trivial trivial ⟨(3, 5), trivial, trivial⟩ ==
      some (#[3, 5, 3, 5] ++ cache ++ basis ++ tail, #[77], 4, 91, 9, 0, true) do
    throwError "Schnorr setup lost challenge copies, basis, empty cache, flags, framing or its time bound"
  unless execute layout trivial trivial ⟨(13, 17), trivial, trivial⟩ ==
      some (#[13, 17, 13, 17] ++ cache ++ basis ++ tail, #[77], 4, 91, 9, 0, true) do
    throwError "Schnorr setup embedded a fixed challenge instead of reading runtime input"
  unless execute emptyLayout trivial trivial ⟨(3, 5), trivial, trivial⟩ ==
      some (#[3, 5, 3, 5] ++ Array.replicate 7 0 ++ #[2, 1, 0, 0, 1, 0, 0, 0],
        #[77], 4, 91, 9, 0, true) do
    throwError "zero-query Schnorr setup lost its two basis entries or final-target cache slot"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``CaliperBackend.SchnorrAGM.Layouts.encoded_valid,
      ``CaliperBackend.SchnorrAGM.Setup.implementation, ``CaliperBackend.SchnorrAGM.Setup.bounded,
      ``CaliperBackend.SchnorrAGM.Setup.names, ``CaliperBackend.SchnorrAGM.Setup.initial_source,
      ``CaliperBackend.SchnorrAGM.messages_handler, ``CaliperBackend.SchnorrAGM.messages_simulate,
      ``CaliperBackend.SchnorrAGM.Layouts.simulate_reserved, ``CaliperBackend.SchnorrAGM.Layouts.Reserved.encoded,
      ``CaliperBackend.SchnorrAGM.Layouts.finish_encoded, ``CaliperBackend.SchnorrAGM.Layouts.run_encoded,
      ``bounded, ``memory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrAGMSetup
