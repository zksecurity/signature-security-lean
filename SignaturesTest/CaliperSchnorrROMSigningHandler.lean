import Signatures.Runtime.Caliper.SchnorrROMSigningHandlerMemory
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMSigningHandler
open SchnorrROMTape SchnorrROM.Signing

private instance : SMul (Word 16) (Word 16) := ⟨fun scalar point => scalar * point⟩
private def tapeLayout : SchnorrROMTape.Layouts 16 (Word 16) where
  scalar := Layout.all (wordRepresentation 16 (by decide))
  capacity := 6
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def sampler : PrivateSampler.Layouts 16 (Word 16) Unit where
  tape := tapeLayout
  state := Pairing.unitRepresentation 16
  fits := by decide
private def initial (_ : tapeLayout.unit.Value) : PrivateSampler.Head sampler :=
  .inr (⟨7, by change 7 < 65534; decide⟩, ())
private def advance (value : Unit × PrivateSampler.Response sampler) : PrivateSampler.Head sampler :=
  .inl ⟨BitVec.ofNat 16 value.2.val.2, trivial⟩
private def initialCode : Realizer .unit tapeLayout.unit.representation (CallerStep.next (PrivateSampler.step sampler)) initial :=
  Assembly.realizer .unit (by decide) _ _ initial [.literal 1, .literal 7] (by decide)
    rfl (by simp [Assembly.Operand.NamesFit])
    (by intro _ _ _ operand member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> trivial)
    (fun _ _ _ => rfl)
private def continuation : Realizer .unit (CallerStep.resume (PrivateSampler.step sampler))
    (CallerStep.next (PrivateSampler.step sampler)) advance :=
  Assembly.realizer .unit (by decide) _ _ advance [.literal 0, .read 0 1] (by decide)
    rfl (by simp [Assembly.Operand.NamesFit])
    (by
      intro value before holds operand member
      have size := Assembly.represented_size _ holds
      change (before.bufs 0).size = 2 at size
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [Assembly.Operand.Valid, size])
    (by
      intro value before holds
      have contents : before.bufs 0 = #[BitVec.ofNat 16 value.2.val.1, BitVec.ofNat 16 value.2.val.2] :=
        Array.toList_inj.mp holds.2.1
      change [0, (before.bufs 0)[1]?.getD 0] = _
      rw [contents]
      rfl)
private def caller : PrivateSampler.Caller sampler :=
  ⟨initial, advance, initialCode, continuation, by decide, by decide⟩
private theorem local_time (value) : continuation.time value ≤ 16 := Assembly.code_time_unit_le _
private theorem initial_time (value) : initialCode.time value ≤ 16 := Assembly.code_time_unit_le _
private theorem local_names : NamesAccounted continuation.code 3 := by constructor <;> decide +kernel
private theorem initial_names : NamesAccounted initialCode.code 3 := by constructor <;> decide +kernel

private def layout : Handler.Layouts 16 Nat (Word 16) (Word 16) Unit where
  sampler := sampler
  point := Layout.all (wordRepresentation 16 (by decide))
  message := Layout.counter 16 256 (by decide) (by decide)
  capacityPred := 2
  countFits := by decide
  storageFits := by decide
private def scale : Implementation .unit layout.core.arithmetic.scaleArgs layout.core.point (fun input => input.1 • input.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .mul (by decide)).viewInput layout.core.arithmetic.scaleArgs.representation
    (fun input => input.val) (fun _ => rfl)).viewOutput layout.core.point.representation
      (fun input => ⟨input.val.1 * input.val.2, trivial⟩) (fun _ => rfl)
private def sub : Implementation .unit layout.core.arithmetic.points layout.core.point (fun input => input.1 - input.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .sub (by decide)).viewInput layout.core.arithmetic.points.representation
    (fun input => input.val) (fun _ => rfl)).viewOutput layout.core.point.representation
      (fun input => ⟨input.val.1 - input.val.2, trivial⟩) (fun _ => rfl)
private theorem scaleBound : scale.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem subBound : sub.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem scaleNames : NamesBound scale.program.code 3 := ⟨by decide, by decide⟩
private theorem subNames : NamesBound sub.program.code 3 := ⟨by decide, by decide⟩
private def program := Handler.code layout trivial scale sub scaleNames.buffers subNames.buffers (by decide) caller 1
private theorem bounded : Interactive.TimeBoundOn (Handler.ready layout 1) (Fresh.port tapeLayout) .unit layout.input.representation
    program (Handler.timeBudget layout trivial 16 16 1 6 6) :=
  Handler.time_bound layout trivial scale sub scaleNames.buffers subNames.buffers (by decide) caller 1 16 16
    local_time initial_time scaleBound subBound
private theorem stored : (program.lower (Fresh.port tapeLayout)).descriptionWords ≤ Handler.codeBudget layout trivial caller 1 27 27 :=
  Handler.code_bound layout trivial scale sub scaleNames.buffers subNames.buffers (by decide) caller 1 scaleBound subBound
private theorem named : WordIO.NamesAccounted (program.lower (Fresh.port tapeLayout)) (Handler.nameBudget layout trivial 3 3) :=
  Handler.names layout trivial scale sub scaleNames.buffers subNames.buffers (by decide) caller 1 3 3
    local_names initial_names scaleNames.accounted subNames.accounted
private theorem accepted : (program.lower (Fresh.port tapeLayout)).DescriptionFits :=
  Handler.descriptionFits layout trivial scale sub scaleNames.buffers subNames.buffers (by decide) caller 1 (by decide) (by decide)
private theorem bufferBound : (program.lower (Fresh.port tapeLayout)).memBound ≤ 11 :=
  Handler.buffers layout trivial scale sub scaleNames.buffers subNames.buffers (by decide) caller 1

private instance (value : Nat × Schnorr.ListROM.Shared.Store (Word 16) (Word 16) Nat) : Decidable (layout.input.valid value) := by
  change Decidable ((value.1 < 256 ∧
    (((True ∧ True) ∧ (value.2.1.2.1.length ≤ 3 ∧ ∀ entry ∈ value.2.1.2.1, (entry.1.1 < 256 ∧ True) ∧ True) ∧
      (value.2.1.2.2.length ≤ 3 ∧ ∀ entry ∈ value.2.1.2.2, (entry.1.1 < 256 ∧ True) ∧ True)) ∧
      (value.2.2.1.length ≤ 6 ∧ ∀ cell ∈ value.2.2.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
      (value.2.2.2.length ≤ 6 ∧ ∀ cell ∈ value.2.2.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536))) ∧
    value.2.1.2.1.length ≤ 2)
  infer_instance

private def saved : List (Schnorr.TapeCell (Word 16)) := [(3, 0, 1)]
private def live : Table Nat (Word 16) (Word 16) := [((7, 11), 0), ((8, 9), 4)]
private def managed : Table Nat (Word 16) (Word 16) := [((5, 6), 1)]
private def run (message : Nat) (cache : Table Nat (Word 16) (Word 16))
    (remaining : List (Schnorr.TapeCell (Word 16))) (replies : List (Word 16)) := do
  let raw := (message, ((3, 5), cache, live), saved, remaining)
  let input : layout.input.Value ← if valid : layout.input.valid raw then some ⟨raw, valid⟩ else none
  let initial := layout.input.representation.initial input
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 1000000 (program.lower (Fresh.port tapeLayout)) before replies
  let decoded := (layout.output.representation.encoding.decode (result.state.bufs 0).toList).map Subtype.val
  pure (decoded, result.trace, result.remaining, result.state.bufs 200, result.state.caps 200,
    result.state.regs 99, result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ Handler.timeBudget layout trivial 16 16 1 6 6))

open Lean in
run_cmd do
  let tail : List (Schnorr.TapeCell (Word 16)) := [(1, 22, 0)]
  let inserted : Table Nat (Word 16) (Word 16) := [((7, 11), 2), ((5, 6), 1)]
  unless run 7 managed ([(9, 0, 2), (9, 0, 7)] ++ tail) [88] ==
      some (some ((11, 7), ((3, 5), inserted, live), saved, tail), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "signing did not preserve LIVE and the caller frame while replaying both draws and inserting in managed"
  let cachedZero : Table Nat (Word 16) (Word 16) := [((7, 11), 0), ((7, 11), 9)]
  unless run 7 cachedZero ([(9, 0, 2), (9, 0, 7)] ++ tail) [88] ==
      some (some ((11, 7), ((3, 5), cachedZero, live), saved, tail), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "the wrapper overwrote a cached zero or duplicate key"
  unless run 7 managed tail [7, 2, 7, 7, 88] ==
      some (some ((11, 7), ((3, 5), inserted, live), saved ++ [(9, 0, 2), (9, 0, 7)], tail),
        [.output 7, .invoke, .input 7, .input 2, .output 7, .invoke, .input 7, .input 7], [88], #[77], 4, 91, 9, true, true) do
    throwError "signing failed to append both fresh samples to the shared tape in order"
  unless run 7 managed ([(9, 0, 2)] ++ tail) [7, 7, 88] ==
      some (some ((11, 7), ((3, 5), inserted, live), saved ++ [(9, 0, 7)], tail),
        [.output 7, .invoke, .input 7, .input 7], [88], #[77], 4, 91, 9, true, true) do
    throwError "signing lost the replay/fresh boundary between its two samples"
  unless run 8 [] ([(9, 0, 0), (9, 0, 0)] ++ tail) [88] ==
      some (some ((0, 0), ((3, 5), [((8, 0), 0)], live), saved, tail), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "zero scalars or a changed message did not reach the signing core"
  unless run 7 managed tail [7, 2] == none do throwError "signing succeeded without its second fresh reply"
  unless run 256 managed tail [] == none do throwError "unrepresented message was admitted"
  unless run 7 (List.replicate 3 ((0, 0), 0)) tail [] == none do throwError "managed insertion reserve was not enforced"
  unless run 7 managed (List.replicate 7 (9, 0, 0)) [] == none do throwError "oversized replay tape was admitted"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Handler.prepare, ``Handler.prepareCore, ``Handler.finish, ``Handler.refines,
      ``Handler.source_original, ``Handler.observe_original, ``Handler.preserves_live, ``Handler.managed_length,
      ``Handler.reserved_after, ``Handler.time_bound, ``Handler.code_bound, ``Handler.names, ``Handler.buffers,
      ``Handler.descriptionFits, ``Handler.resources, ``bounded, ``stored, ``named, ``accepted, ``bufferBound] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMSigningHandler
