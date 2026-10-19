import Signatures.Runtime.Caliper.CallerStepBounds
import Signatures.Runtime.Caliper.UniformQuery
import Signatures.Runtime.Caliper.Words
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend

namespace SignaturesTest.CaliperCaller

private def word := wordRepresentation 10 (by decide)
private def port := UniformQuery.port (w := 10) 3 (by decide) (by decide)
private def layout : CallerStep.Layouts 10 (Word 10) (Fin 4) (UniformQuery.Reply 3) (Word 10) (Word 10) :=
  ⟨word, port.request, port.reply, word, word, by decide, by decide⟩

private def sampled (reply : UniformQuery.Reply 3) : Fin 4 :=
  ⟨reply.2.val, by have := reply.1.isLt; have := reply.2.isLt; omega⟩

private def advance (value : Word 10 × UniformQuery.Reply 3) : Word 10 ⊕ (Fin 4 × Word 10) :=
  .inr (sampled value.2, value.1)

-- A real caller continuation chooses its next request from the last answer.
-- This is a regression fixture; the library theorem quantifies over arbitrary
-- continuation code with its own correctness and resource proof.
private def continuation : Realizer .unit (CallerStep.resume layout) (CallerStep.next layout) advance :=
  Assembly.realizer .unit (by decide) _ _ advance [.literal 1, .read 0 2, .read 0 0] (by decide)
    rfl (by simp [Assembly.Operand.NamesFit])
    (by
      intro value before holds operand member
      have size := Assembly.represented_size _ holds
      change (before.bufs 0).size = 3 at size
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> simp [Assembly.Operand.Valid, size])
    (by
      intro value before holds
      have contents : before.bufs 0 = #[value.1, BitVec.ofNat 10 value.2.1.val, BitVec.ofNat 10 value.2.2.val] :=
        Array.toList_inj.mp holds.2.1
      change [1, (before.bufs 0)[2]?.getD 0, (before.bufs 0)[0]?.getD 0] =
        [1, BitVec.ofNat 10 value.2.2.val, value.1]
      rw [contents]
      rfl)

private def handler := UniformQuery.forward 3 (by decide) (by decide) word
private def step := CallerStep.code layout port advance continuation (by decide) handler
private def route := SumContext.distribute word (CallerStep.pending layout) word (by decide) (by decide)
private def result := word.prod word (by decide)
private def body : Interactive.Code 10 := .seq step (.compute route.code)
private def bodySource (value : (Fin 4 × Word 10) × Word 10) : ProbComp ((Word 10 × Word 10) ⊕ ((Fin 4 × Word 10) × Word 10)) :=
  SumContext.view <$> CallerStep.denote advance (UniformQuery.forwardSource 3) value
private def stop : Realizer .unit (CallerStep.frame layout) result (fun value => (value.1.2, value.2)) :=
  selectSliceRealizer .unit (by decide) (CallerStep.frame layout) result _ 1 (by decide) (by decide) (fun _ => rfl)
private def program (fuel : Nat) := Interactive.loop body (.compute stop.code) 2 3 fuel
private def invariant (remaining : Nat) (value : (Fin 4 × Word 10) × Word 10) := value.1.1.val + remaining ≤ 5

private theorem step_refines : Interactive.RefinesOn (fun _ => True) port .unit (CallerStep.frame layout)
    (CallerStep.output layout) (CallerStep.denote advance (UniformQuery.forwardSource 3)) step :=
  CallerStep.refines layout port advance continuation (by decide)
    ((UniformQuery.forward_refines 3 (by decide) (by decide) word (by decide)).on (fun _ => True))

private theorem body_refines : Interactive.RefinesOn (fun _ => True) port .unit (CallerStep.frame layout)
    (result.sum (CallerStep.frame layout) (by decide) (by decide)) bodySource body := by
  have refined := step_refines.seq ((Interactive.Refines.compute port .unit route).on (fun _ => True)) (by intros; trivial)
  change Interactive.RefinesOn _ _ _ _ (SumContext.output word (CallerStep.pending layout) word (by decide) (by decide)) _ _
  unfold bodySource body
  simpa only [bind_pure_comp] using refined

private theorem preserves (remaining : Nat) (value : (Fin 4 × Word 10) × Word 10)
    (valid : invariant (remaining + 1) value) (answer) (reached : answer ∈ support (bodySource value)) :
    Sum.elim (fun _ => True) (invariant remaining) answer := by
  simp only [bodySource, CallerStep.denote, UniformQuery.forwardSource, UniformQuery.source, Functor.map_map,
    support_map, Set.mem_image] at reached
  obtain ⟨draw, _, rfl⟩ := reached
  change draw.val + remaining ≤ 5
  have bounded := draw.isLt
  unfold invariant at valid
  omega

private theorem program_refines (fuel : Nat) : Interactive.RefinesOn (invariant fuel) port .unit
    (CallerStep.frame layout) result (BackendProgram.loopDenote bodySource (fun value => pure (value.1.2, value.2)) fuel)
    (program fuel) :=
  Interactive.RefinesOn.loop (CallerStep.frame layout) result invariant (by decide) (by decide)
    (fun _ tape value _ before holds => body_refines tape value trivial before holds)
    ((Interactive.Refines.compute port .unit stop).on (invariant 0)) preserves fuel

private theorem step_time : Interactive.TimeBoundOn (fun _ => True) port .unit (CallerStep.frame layout) step 1606 := by
  exact CallerStep.time layout port advance continuation (by decide)
    ((UniformQuery.forward_refines 3 (by decide) (by decide) word (by decide)).on (fun _ => True))
    ((UniformQuery.forward_time 3 (by decide) (by decide) word (by decide)).on (fun _ => True))
    (show ∀ value, continuation.time value ≤ 1000 from by intro value; change continuation.time (0, ⟨(0 : Fin 4), (0 : Fin 1)⟩) ≤ 1000; decide)

private theorem body_time : Interactive.TimeBoundOn (fun _ => True) port .unit (CallerStep.frame layout) body 1704 := by
  exact Interactive.TimeBoundOn.seq step_refines step_time
    ((Interactive.TimeBound.compute (port := port) (cost := .unit) route 98
      (SumContext.time word (CallerStep.pending layout) word (by decide) (by decide))).on (fun _ => True))
    (by intros; trivial)

private theorem program_time (fuel : Nat) : Interactive.TimeBoundOn (invariant fuel) port .unit
    (CallerStep.frame layout) (program fuel) (16 + fuel * 1730) := by
  exact Interactive.TimeBoundOn.loop (CallerStep.frame layout) result invariant (by decide) (by decide)
    (fun _ tape value _ before holds => body_refines tape value trivial before holds)
    (fun _ tape value _ before holds => body_time tape value trivial before holds)
    ((Interactive.TimeBound.compute (port := port) (cost := .unit) stop 16 (fun _ => by change stop.time ((0, 0), 0) ≤ 16; decide)).on (invariant 0)) preserves fuel

example : (step.lower port).descriptionWords ≤ (handler.lower port).descriptionWords + descriptionWords continuation.code + 260 * CallerStep.width layout + 128 :=
  CallerStep.words layout port advance continuation (by decide) handler
example : (step.lower port).DescriptionFits := CallerStep.descriptionFits layout port advance continuation (by decide)
  (UniformQuery.forward_descriptionFits 3 (by decide) (by decide) word (by decide)) (by decide)
example : WordIO.NamesAccounted (step.lower port) 16 := CallerStep.names layout port advance continuation (by decide)
  ((UniformQuery.forward_names 3 (by decide) (by decide) word).accounted.mono (by decide))
  (show NamesAccounted continuation.code 16 from ⟨by decide, by decide⟩)

-- Both unequal-width branches must move the saved word to the proper position:
-- input [tag, payload, padding, saved] is not the output's byte layout.
private def routingResult (value : (Word 10 ⊕ (Fin 4 × Word 10)) × Word 10) :=
  (WordIO.run .unit RandomTape.zero 1000 (.compute route.code)
    ((SumContext.input word (CallerStep.pending layout) word (by decide) (by decide)).initial value) []).map
      (fun finished => finished.state.bufs 0)

private def start : State 10 :=
  let state := (CallerStep.frame layout).initial ((3, 77), 88)
  { state with bufs := fun b => if b = 200 then #[91] else state.bufs b
               caps := fun b => if b = 200 then 4 else state.caps b
               regs := fun r => if r = 200 then 99 else state.regs r
               tapePos := 9 }

private def execute (fuel : Nat) (replies : List (Word 10)) :=
  (WordIO.run .unit RandomTape.zero 10000 ((program fuel).lower port) start replies).map
    (fun finished => (finished.state.bufs 0, finished.trace, finished.remaining,
      finished.state.bufs 200, finished.state.caps 200, finished.state.regs 200, finished.state.tapePos))

open Lean in
run_cmd do
  unless routingResult (.inl 7, 88) == some #[0, 7, 88, 0] do
    throwError "caller routing left padding crossed the saved state incorrectly"
  unless routingResult (.inr (2, 77), 88) == some #[1, 2, 77, 88] do
    throwError "caller routing right branch lost saved state"
  unless execute 0 [55] == some (#[77, 88], [], [55], #[91], 4, 99, 9) do
    throwError "zero-fuel caller should return without querying"
  unless execute 2 [3, 2, 2, 1, 55] == some (#[77, 88],
      [.output 3, .invoke, .input 3, .input 2, .output 2, .invoke, .input 2, .input 1], [55], #[91], 4, 99, 9) do
    throwError "caller continuation did not route the sampled next request or preserve both states"
  unless execute 2 [3, 0, 0, 0, 55] == some (#[77, 88],
      [.output 3, .invoke, .input 3, .input 0, .output 0, .invoke, .input 0, .input 0], [55], #[91], 4, 99, 9) do
    throwError "caller zero-range follow-up failed"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``SumContext.time, ``SumContext.words, ``SumContext.names, ``CallerStep.refines,
      ``CallerStep.time, ``CallerStep.words, ``CallerStep.names, ``CallerStep.descriptionFits,
      ``Interactive.RefinesOn.loop, ``Interactive.TimeBoundOn.loop, ``Interactive.RefinesOn.resources,
      ``program_refines, ``program_time] do
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperCaller
