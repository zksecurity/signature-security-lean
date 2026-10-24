import Proofs.Runtime.Caliper.SchnorrROMCallerResources
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMCallerControl
open SchnorrROMTape SchnorrROM

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance : SMul (ZMod 7) (Word 16) := ⟨fun scalar point => BitVec.ofNat 16 scalar.val * point⟩
private def params : PrivateSampler.Enumerated.Parameters 16 (ZMod 7) :=
  PrivateSampler.Enumerated.Parameters.ofFinEnum 16 (ZMod 7) 12 (by decide) (by decide) (by decide)
private def config : Signing.Enumerated.Configuration 16 Nat (ZMod 7) (Word 16) where
  sampler := params
  message := Layout.counter 16 256 (by decide) (by decide)
  point := Layout.all (wordRepresentation 16 (by decide))
  capacityPred := 2
  countFits := by decide
  storageFits := by decide
private def scale : Implementation .unit config.handler.core.arithmetic.scaleArgs config.handler.core.point (fun value => value.1 • value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .mul (by decide)).viewInput config.handler.core.arithmetic.scaleArgs.representation
    (fun value => (BitVec.ofNat 16 value.val.1.val, value.val.2)) (fun _ => rfl)).viewOutput config.handler.core.point.representation
      (fun value => ⟨value.val.1 • value.val.2, trivial⟩) (fun _ => rfl)
private def sub : Implementation .unit config.handler.core.arithmetic.points config.handler.core.point (fun value => value.1 - value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .sub (by decide)).viewInput config.handler.core.arithmetic.points.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput config.handler.core.point.representation
      (fun value => ⟨value.val.1 - value.val.2, trivial⟩) (fun _ => rfl)
private theorem scaleBound : scale.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem subBound : sub.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private def operations : Handler.Operations config where
  scale := scale
  sub := sub
  slots := 3
  scaleNames := ⟨by decide, by decide⟩
  subNames := ⟨by decide, by decide⟩
  reserve := by decide
  signing := Handler.fullField config scale sub ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) scaleBound subBound
private def budget : Handler.Budget config operations where
  scaleTime := 6
  scaleWords := 27
  subTime := 6
  subWords := 27
  scale := scaleBound
  sub := subBound

private abbrev Store := Schnorr.ListROM.Shared.Store (ZMod 7) (Word 16) Nat
private abbrev Query := (Nat ⊕ (Nat × Word 16)) ⊕ Nat
private instance (value : Store) : Decidable (config.handler.store.valid value) := by
  change Decidable ((((True ∧ True) ∧
    (value.1.2.1.length ≤ 3 ∧ ∀ entry ∈ value.1.2.1, (entry.1.1 < 256 ∧ True) ∧ True) ∧
    (value.1.2.2.length ≤ 3 ∧ ∀ entry ∈ value.1.2.2, (entry.1.1 < 256 ∧ True) ∧ True)) ∧
    (value.2.1.length ≤ 12 ∧ ∀ cell ∈ value.2.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
    (value.2.2.length ≤ 12 ∧ ∀ cell ∈ value.2.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536)))
  infer_instance
private def word := wordRepresentation 16 (by decide)
private abbrev Head := Word 16 ⊕ (CallerPackets.Request config × Word 16)
private def layout := Caller.layout config word word (by decide)
private def advance (value : Word 16 × CallerPackets.Reply config) : Head := .inl value.1
private def continuation : Realizer .unit (CallerStep.resume layout) (CallerStep.next layout) advance :=
  ((firstRealizer .unit (by decide) word (CallerPackets.reply config) (by decide) (by decide)).then
    (inlRealizer .unit (by decide) word (CallerStep.pending layout) (by decide) (by decide))).viewOutput
      (CallerStep.next layout) advance (fun _ => rfl)
private def routines : Caller.Routines config (Word 16) (Word 16) Head where
  state := word
  result := word
  fits := by decide
  advance := advance
  continuation := continuation
  localNameFits := by decide
  input := CallerStep.next layout
  initial := id
  initialization := Realizer.identity (by decide) (CallerStep.next layout)
  initialNameFits := by decide
  inputFits := by decide
private def localBudget : Caller.LocalBudget config routines where
  localTime := 1000
  initialTime := 0
  localWords := 10000
  initialWords := 1
  local_time value := by
    change continuation.time (0, .inl (.inr ⟨0, trivial⟩)) ≤ 1000
    decide
  initial_time _ := Nat.le_refl _
  local_words := by decide +kernel
  initial_words := by decide

-- A second local routine uses each random reply as the next request's range.
-- The other reply variants have zero padding in the same input position.
private def sampled : CallerPackets.Reply config → (SchnorrROMTape.Reply.range config.handler.sampler.tape).Value
  | .inl (.inl value) => ⟨value.val.2, by
      have bound := value.property.1.1
      have answer := value.property.2
      exact lt_of_le_of_lt answer bound⟩
  | .inl (.inr _) => ⟨0, by change 0 < 65534; decide⟩
  | .inr _ => ⟨0, by change 0 < 65534; decide⟩
private def adaptive (value : Word 16 × CallerPackets.Reply config) : Head := .inr (.inl (.inl (sampled value.2)), value.1)
private def adaptiveCode : Realizer .unit (CallerStep.resume layout) (CallerStep.next layout) adaptive :=
  Assembly.realizer .unit (by decide) _ _ adaptive
    [.literal 1, .literal 0, .literal 0, .read 0 4, .literal 0, .read 0 0] (by decide)
    rfl (by simp [Assembly.Operand.NamesFit])
    (by
      intro value before holds operand member
      have size := Assembly.represented_size _ holds
      change (before.bufs 0).size = 5 at size
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Assembly.Operand.Valid, size])
    (by
      intro value before holds
      have contents := Array.toList_inj.mp holds.2.1
      change [1, 0, 0, (before.bufs 0)[4]?.getD 0, 0, (before.bufs 0)[0]?.getD 0] = _
      rw [contents]
      rcases value with ⟨state, (reply | reply) | reply⟩ <;> rfl)
private def adaptiveRoutines : Caller.Routines config (Word 16) (Word 16) Head :=
  { routines with advance := adaptive, continuation := adaptiveCode, localNameFits := by decide }
private def adaptiveBudget : Caller.LocalBudget config adaptiveRoutines where
  localTime := 1000
  initialTime := 0
  localWords := 10000
  initialWords := 1
  local_time value := by
    change adaptiveCode.time (0, .inl (.inr ⟨0, trivial⟩)) ≤ 1000
    decide
  initial_time _ := Nat.le_refl _
  local_words := by decide +kernel
  initial_words := by decide

example (fuel : Nat) : ((Caller.program config routines operations fuel).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  Caller.descriptionFits config routines operations fuel
example (fuel : Nat) : Interactive.RefinesOn (Caller.admitted config fuel) (Fresh.port config.handler.sampler.tape) .unit
    (adaptiveRoutines.inputLayout config) (adaptiveRoutines.outputLayout config)
    (Caller.source config adaptiveRoutines operations fuel) (Caller.program config adaptiveRoutines operations fuel) :=
  Caller.refines config adaptiveRoutines operations fuel
private theorem localNames : NamesAccounted routines.continuation.code 3 :=
  (⟨by decide, by decide⟩ : NamesBound routines.continuation.code 3).accounted
example (fuel : Nat) : WordIO.NamesAccounted
    ((Caller.program config routines operations fuel).lower (Fresh.port config.handler.sampler.tape)) (Handler.nameBudget config operations) :=
  Caller.names config routines operations _ le_rfl (localNames.mono (by unfold Handler.nameBudget; omega)) (skip_names _) fuel

private instance (fuel : Nat) (saved : Store) : Decidable (Handler.Reserved config fuel saved) := by
  unfold Handler.Reserved
  infer_instance
private def store (saved remaining : List (Schnorr.TapeCell (ZMod 7)) := []) : Store := (((3, 5), [], []), saved, remaining)
private def pending (range : Fin 65534) (state : Word 16 := 55) : Head := .inr (.inl (.inl ⟨range.val, range.isLt⟩), state)
private def observe (value : CallerControl.Packet (Word 16) (CallerPackets.Request config) (Word 16) config.handler.store.Value) :=
  (value.1.map id (fun pending => (CallerHandler.query config pending.1, pending.2)), value.2.val)
private def run (r : Caller.Routines config (Word 16) (Word 16) Head) (b : Caller.LocalBudget config r)
    (fuel : Nat) (head : Head) (saved : Store) (replies : List (Word 16)) := do
  if valid : config.handler.store.valid saved then
    if !(decide (Handler.Reserved config fuel saved)) then none else do
      let initial := (r.inputLayout config).initial (head, ⟨saved, valid⟩)
      let before := { initial with
        bufs := fun i => if i = 200 then #[77] else initial.bufs i
        caps := fun i => if i = 200 then 4 else initial.caps i
        regs := fun i => if i = 99 then 91 else initial.regs i
        tapePos := 9 }
      let result ← WordIO.run .unit RandomTape.zero 1000000
        ((Caller.program config r operations fuel).lower (Fresh.port config.handler.sampler.tape)) before replies
      pure (((r.outputLayout config).encoding.decode (result.state.bufs 0).toList).map observe,
        result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
        result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
        decide (result.time ≤ Caller.timeBudget config r operations budget b fuel))
  else none

private def groupConfig : Signing.Enumerated.Configuration 16 Nat (ZMod 7) (ZMod 7) where
  sampler := params
  message := config.message
  point := PrivateSampler.Enumerated.scalar params
  capacityPred := 2
  countFits := by decide
  storageFits := by decide
private theorem original_sampler (target : Schnorr.ListROM.Handler (ZMod 7) (ZMod 7) (ZMod 7) Nat Nat)
    (q : (Nat ⊕ (Nat × ZMod 7)) ⊕ Nat) :
    Caller.original groupConfig target q = Schnorr.ListROM.Shared.interpret (target q) := by
  have same : PrivateSampler.Enumerated.sampleable groupConfig.sampler = FinEnum.SampleableType (ZMod 7) :=
    PrivateSampler.Enumerated.sampleable_finEnum 12 (by decide) (by decide) (by decide)
  unfold Caller.original
  rw [same]

open Lean in
run_cmd do
  for fuel in [0, 2] do
    unless run routines localBudget fuel (.inl 7) (store) [88] ==
        some (some (.inl 7, store), [], [88], #[77], 4, 91, 9, true, true) do
      throwError "ROM caller failed immediate return or touched the private store"
  unless run routines localBudget 0 (pending 7) (store) [88] ==
      some (some (.inr (.inl (.inl 7), 55), store), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "zero-fuel ROM caller confused pending cutoff with a return"
  let after := store [(9, 0, 4)]
  for fuel in [1, 2] do
    unless run routines localBudget fuel (pending 7) (store) [7, 4, 88] ==
        some (some (.inl 55, after), [.output 7, .invoke, .input 7, .input 4], [88], #[77], 4, 91, 9, true, true) do
      throwError "ROM caller failed one call or continued past early return"
  unless run adaptiveRoutines adaptiveBudget 2 (pending 7) (store) [7, 4, 4, 2, 88] ==
      some (some (.inr (.inl (.inl 2), 55), store [(9, 0, 4), (6, 0, 2)]),
        [.output 7, .invoke, .input 7, .input 4, .output 4, .invoke, .input 4, .input 2],
        [88], #[77], 4, 91, 9, true, true) do
    throwError "adaptive ROM caller lost its reply-dependent range, continuation state or fuel cutoff"
  unless run adaptiveRoutines adaptiveBudget 2 (pending 7) (store [] [(9, 0, 10), (4, 0, 5)]) [88] ==
      some (some (.inr (.inl (.inl 2), 55), store), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "adaptive ROM replay changed private-family decoding or the saved tape"
  unless run routines localBudget 1 (.inr (.inl (.inr ⟨(9, 9), by change 9 < 256; decide, trivial⟩), 55)) (store) [6, 0, 88] ==
      some (some (.inl 55, (((3, 5), [((9, 9), 0)], [((9, 9), 0)]), [(1, 0, 0)], [])),
        [.output 6, .invoke, .input 6, .input 0], [88], #[77], 4, 91, 9, true, true) do
    throwError "ROM caller hash branch lost the complete updated store"
  unless run routines localBudget 1 (.inr (.inr ⟨7, by change 7 < 256; decide⟩, 55)) (store) [6, 3, 6, 6, 88] ==
      some (some (.inl 55, (((3, 5), [((7, 3), 3)], []), [(8, 0, 3), (8, 0, 6)], [])),
        [.output 6, .invoke, .input 6, .input 3, .output 6, .invoke, .input 6, .input 6],
        [88], #[77], 4, 91, 9, true, true) do
    throwError "ROM caller signing branch lost private-draw order or programmed cache state"
  unless run adaptiveRoutines adaptiveBudget 2 (pending 7) (store) [7, 4] == none &&
      run routines localBudget 3 (pending 7) (store) [] == none do
    throwError "ROM caller accepted missing replies or insufficient remaining-call reserve"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Caller.refines, ``Caller.available, ``Caller.preserves, ``Caller.initial_invariant,
      ``Caller.start_postcondition, ``Caller.execution_postcondition, ``Caller.Postcondition.final_hash,
      ``Caller.source_original, ``Caller.observe_source, ``Caller.time, ``Caller.words, ``Caller.names,
      ``Caller.handlerNameFits, ``Caller.descriptionFits, ``Caller.resources, ``original_sampler] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMCallerControl
