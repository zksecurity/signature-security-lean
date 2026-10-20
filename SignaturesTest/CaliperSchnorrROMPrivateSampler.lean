import Signatures.Runtime.Caliper.SchnorrROMPrivateSamplerBounds
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMPrivateSampler
open SchnorrROMTape

private def tapeLayout : SchnorrROMTape.Layouts 12 Nat where
  scalar := Layout.counter 12 4096 (by decide) (by decide)
  capacity := 6
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private theorem zeroValid : tapeLayout.scalar.valid 0 := by change 0 < 4096; decide
private def layout : PrivateSampler.Layouts 12 Nat Bool where
  tape := tapeLayout
  state := Representation.boolean 12 (by decide)
  fits := by decide
private def initial (_ : tapeLayout.unit.Value) : PrivateSampler.Head layout :=
  .inr (⟨7, by change 7 < 4094; decide⟩, true)
private def followup (reply : PrivateSampler.Response layout) : PrivateSampler.Request layout :=
  ⟨reply.val.2, by
    have bound : reply.val.1 < 4094 := reply.property.1.1
    have := reply.property.2
    change reply.val.2 < 4094
    omega⟩
private def advance (value : Bool × PrivateSampler.Response layout) : PrivateSampler.Head layout :=
  if value.1 then .inr (followup value.2, false) else .inl ⟨value.2.val.2, value.2.property.1.2⟩

private def initialCode : Realizer .unit tapeLayout.unit.representation (CallerStep.next (PrivateSampler.step layout)) initial :=
  Assembly.realizer .unit (by decide) _ _ initial [.literal 1, .literal 7, .literal 1] (by decide)
    rfl (by simp [Assembly.Operand.NamesFit])
    (by intro _ _ _ operand member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> trivial)
    (fun _ _ _ => rfl)
private def continuation : Realizer .unit (CallerStep.resume (PrivateSampler.step layout))
    (CallerStep.next (PrivateSampler.step layout)) advance :=
  Assembly.realizer .unit (by decide) _ _ advance [.read 0 0, .read 0 2, .literal 0] (by decide)
    rfl (by simp [Assembly.Operand.NamesFit])
    (by
      intro value before holds operand member
      have size := Assembly.represented_size _ holds
      change (before.bufs 0).size = 3 at size
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> simp [Assembly.Operand.Valid, size])
    (by
      intro value before holds
      have contents : before.bufs 0 =
          #[if value.1 then 1 else 0, BitVec.ofNat 12 value.2.val.1, BitVec.ofNat 12 value.2.val.2] :=
        Array.toList_inj.mp holds.2.1
      rcases value with ⟨flag, reply⟩
      cases flag <;>
        change [(before.bufs 0)[0]?.getD 0, (before.bufs 0)[2]?.getD 0, 0] = _ <;>
        rw [contents] <;> rfl)
private def caller : PrivateSampler.Caller layout :=
  ⟨initial, advance, initialCode, continuation, by decide, by decide⟩
private theorem terminates : PrivateSampler.Terminates layout caller 2 := by
  intro value
  change ∀ answer, CallerMachine.Terminates (spec := unifSpec) Subtype.val
    (PrivateSampler.representReply layout) advance 1 (advance (true, PrivateSampler.representReply layout _ answer))
  intro answer
  change ∀ next, True
  intro _
  trivial

private theorem local_time (value) : continuation.time value ≤ 24 := Assembly.code_time_unit_le _
private theorem initial_time (value) : initialCode.time value ≤ 24 := Assembly.code_time_unit_le _
private theorem local_names : NamesAccounted continuation.code 3 := by constructor <;> decide +kernel
private theorem initial_names : NamesAccounted initialCode.code 3 := by constructor <;> decide +kernel
private theorem program_time : Interactive.TimeBoundOn (PrivateSampler.admissible layout 2) (Fresh.port tapeLayout) .unit
    (PrivateSampler.input layout) (PrivateSampler.code layout caller zeroValid 2)
    (PrivateSampler.timeBudget layout zeroValid 24 24 2) :=
  PrivateSampler.time_bound layout caller zeroValid 2 24 24 local_time initial_time
example : ((PrivateSampler.code layout caller zeroValid 2).lower (Fresh.port tapeLayout)).DescriptionFits :=
  PrivateSampler.descriptionFits layout caller zeroValid 2
example : WordIO.NamesAccounted ((PrivateSampler.code layout caller zeroValid 2).lower (Fresh.port tapeLayout))
    (PrivateSampler.nameBudget layout zeroValid 3) :=
  PrivateSampler.names layout caller zeroValid 2 3 local_names initial_names

private def saved : List (Schnorr.TapeCell Nat) := [(3, 0, 1)]
private def run (fuel : Nat) (remaining : List (Schnorr.TapeCell Nat)) (replies : List (Word 12)) := do
  let store : (Read.tapes tapeLayout).Value ←
    if valid : remaining.length ≤ 6 ∧ ∀ cell ∈ remaining,
        cell.1 < 4096 ∧ cell.2.1 < 4096 ∧ cell.2.2 < 4096 then
      some ⟨(saved, remaining), by
        constructor
        · change saved.length ≤ 6 ∧ ∀ cell ∈ saved, cell.1 < 4096 ∧ cell.2.1 < 4096 ∧ cell.2.2 < 4096
          simp [saved]
        · exact valid⟩
    else none
  let initial := (PrivateSampler.input layout).initial (⟨(), trivial⟩, store)
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 1000000
    ((PrivateSampler.code layout caller zeroValid fuel).lower (Fresh.port tapeLayout)) before replies
  let decoded := (CallerStep.output (PrivateSampler.step layout)).encoding.decode (result.state.bufs 0).toList
  let observed := decoded.map (fun p : CallerControl.Packet Bool (PrivateSampler.Request layout)
    tapeLayout.scalar.Value (PrivateSampler.Store layout) => ((CallerControl.answer p).1.map Subtype.val, p.2.val))
  pure (observed, result.trace, result.remaining, result.state.bufs 200, result.state.caps 200,
    result.state.regs 99, result.state.tapePos)

open Lean in
run_cmd do
  let tail : List (Schnorr.TapeCell Nat) := [(1, 22, 0)]
  unless run 2 ([(9, 0, 10), (4, 0, 8)] ++ tail) [88] ==
      some (some (some 2, saved, tail), [], [88], #[77], 4, 91, 9) do
    throwError "adaptive replay did not reduce oversized payloads or preserve challenge cells"
  unless run 2 ([(9, 0, 7), (9, 0, 3)] ++ tail) [88] ==
      some (some (some 3, saved, tail), [], [88], #[77], 4, 91, 9) do
    throwError "same-family adaptive replay lost chronological order"
  unless run 2 ([(9, 0, 10)] ++ tail) [2, 1, 88] ==
      some (some (some 1, saved ++ [(4, 0, 1)], tail),
        [.output 2, .invoke, .input 2, .input 1], [88], #[77], 4, 91, 9) do
    throwError "adaptive hit/miss changed the requested range or the shared saved tape"
  unless run 2 tail [7, 4, 4, 3, 88] ==
      some (some (some 3, saved ++ [(9, 0, 4), (6, 0, 3)], tail),
        [.output 7, .invoke, .input 7, .input 4, .output 4, .invoke, .input 4, .input 3],
        [88], #[77], 4, 91, 9) do
    throwError "two adaptive fresh draws were not recorded in original order"
  unless run 2 tail [7, 0, 0, 0, 88] ==
      some (some (some 0, saved ++ [(9, 0, 0), (2, 0, 0)], tail),
        [.output 7, .invoke, .input 7, .input 0, .output 0, .invoke, .input 0, .input 0],
        [88], #[77], 4, 91, 9) do
    throwError "adaptive zero-range follow-up failed"
  unless run 1 ([(9, 0, 10)] ++ tail) [88] ==
      some (some (none, saved, tail), [], [88], #[77], 4, 91, 9) do
    throwError "exhausted caller fuel was confused with a completed sample"
  unless run 2 tail [] == none do throwError "a private miss succeeded without a uniform reply"
  unless run 2 (List.replicate 7 (9, 0, 0)) [] == none do
    throwError "out-of-capacity input was admitted"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Schnorr.RawTape.Private.simulate_source, ``Schnorr.RawTape.Private.scalar_source,
      ``PrivateQuery.refines, ``PrivateQuery.source_eq, ``PrivateQuery.time_bound, ``PrivateQuery.descriptionFits,
      ``PrivateHandler.synchronizes, ``PrivateHandler.reserved_after,
      ``PrivateSampler.refines, ``PrivateSampler.observe_source, ``PrivateSampler.scalar_source,
      ``PrivateSampler.resources, ``program_time, ``terminates] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMPrivateSampler
