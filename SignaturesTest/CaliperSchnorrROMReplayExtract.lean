import Signatures.Runtime.Caliper.SchnorrROMPassPresentation
import Signatures.Runtime.Caliper.SchnorrROMReplayExtractFullBounds
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMReplayExtract
open SchnorrROMTape SchnorrROM

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance : SMul (ZMod 7) (Word 16) := ⟨fun scalar point => BitVec.ofNat 16 scalar.val * point⟩
private def params : PrivateSampler.Enumerated.Parameters 16 (ZMod 7) :=
  PrivateSampler.Enumerated.Parameters.ofFinEnum 16 (ZMod 7) 18 (by decide) (by decide) (by decide)
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

private abbrev Key := config.point.Value
private def layout := Pass.control config config.point.representation (by decide)
private def forge (key : Key) : (ForgeryHash.forgery config).Value :=
  ⟨(2, key.val, 0), by change 2 < 256; decide, key.property, trivial⟩
private def next (done : Bool) (q : CallerPackets.Request config) (key : Key) :=
  if done then Sum.inl (forge key) else Sum.inr (q, key)
private def parts (done : Bool) (q : CallerPackets.Request config) : List (ByteRoute.Part 16) :=
  if done then [.literal [0, 2], .slice 0 1, .literal [0, 0, 0]]
  else [.literal (1 :: (CallerPackets.request config).encoding.encode q), .slice 0 1]
private theorem parts_size (done : Bool) (q : CallerPackets.Request config) :
    ByteRoute.words (parts done q) = (CallerStep.next layout).encoding.words := by
  cases done <;> simp only [parts, Bool.false_eq_true, ↓reduceIte, ByteRoute.words, List.length_cons, List.length_nil, Encoding.encode_length] <;> rfl
private def initialCode (done : Bool) (q : CallerPackets.Request config) :
    Realizer .unit config.point.representation (CallerStep.next layout) (next done q) :=
  ByteRoute.realizer _ _ _ (parts done q) (by decide)
    (by cases done <;> exact ⟨by decide, trivial⟩) (parts_size done q)
    (by intro key; cases done <;> rcases q with (q | q) | q <;> rfl)
private def advanceCode (q : CallerPackets.Request config) :
    Realizer .unit (CallerStep.resume layout) (CallerStep.next layout)
      (fun value => next true q value.1) :=
  ByteRoute.realizer _ _ _ (parts true q) (by decide) (by exact ⟨by decide, trivial⟩) (parts_size true q)
    (by intro value; rcases value with ⟨key, (answer | answer) | answer⟩ <;> rfl)
private theorem initialize_buffers (done : Bool) (q : CallerPackets.Request config) : (initialCode done q).code.memBound ≤ 2 :=
  ByteRoute.buffers _ _ _ _ _ _ _ _
private theorem continue_buffers (q : CallerPackets.Request config) : (advanceCode q).code.memBound ≤ 2 :=
  ByteRoute.buffers _ _ _ _ _ _ _ _
private def caller (done : Bool) (q : CallerPackets.Request config) : Pass.Caller config Key where
  state := config.point.representation
  fits := by decide
  advance := fun value => next true q value.1
  continuation := advanceCode q
  localNameFits := by have := continue_buffers q; change max 2 (advanceCode q).code.memBound < 65536; omega
  initial := next done q
  initialization := initialCode done q
  initialNameFits := by have := initialize_buffers done q; change max 2 (initialCode done q).code.memBound < 65536; omega
private def localBudget (done : Bool) (q : CallerPackets.Request config) : Caller.LocalBudget config ((caller done q).routines config) where
  localTime := 48
  initialTime := 48
  localWords := 170
  initialWords := 170
  local_time := by
    change ∀ value, (advanceCode q).time value ≤ 48
    exact ByteRoute.time _ _ _ _ _ _ _ _
  initial_time := by
    change ∀ value, (initialCode done q).time value ≤ 48
    exact ByteRoute.time _ _ _ _ _ _ _ _
  local_words := by
    change descriptionWords (advanceCode q).code ≤ 170
    exact ByteRoute.codeWords _ _ _ _ _ _ _ _
  initial_words := by
    change descriptionWords (initialCode done q).code ≤ 170
    exact ByteRoute.codeWords _ _ _ _ _ _ _ _

private def random : CallerPackets.Request config := .inl (.inl ⟨7, by change 7 < 65534; decide⟩)
private def hashed : CallerPackets.Request config := .inl (.inr ⟨(2, 5), by change 2 < 256; decide, trivial⟩)
private def signed : CallerPackets.Request config := .inr ⟨2, by change 2 < 256; decide⟩
private instance (value : Schnorr.ListROM.Shared.Tape (ZMod 7)) : Decidable ((Pass.Initialization.tapes config).valid value) := by
  change Decidable ((value.1.length ≤ 18 ∧ ∀ cell ∈ value.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
    (value.2.length ≤ 18 ∧ ∀ cell ∈ value.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536))
  infer_instance
private abbrev Store := Schnorr.ListROM.Shared.Store (ZMod 7) (Word 16) Nat
private abbrev Observation := Option ((Nat × Word 16 × ZMod 7) × ZMod 7) × Store
private instance : BEq Observation := inferInstance
private instance (value : Store) : Decidable (config.handler.store.valid value) := by
  change Decidable ((((True ∧ True) ∧
    (value.1.2.1.length ≤ 3 ∧ ∀ entry ∈ value.1.2.1, (entry.1.1 < 256 ∧ True) ∧ True) ∧
    (value.1.2.2.length ≤ 3 ∧ ∀ entry ∈ value.1.2.2, (entry.1.1 < 256 ∧ True) ∧ True)) ∧
    (value.2.1.length ≤ 18 ∧ ∀ cell ∈ value.2.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
    (value.2.2.length ≤ 18 ∧ ∀ cell ∈ value.2.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536)))
  infer_instance

private theorem nameRoom (done : Bool) (q : CallerPackets.Request config) : Pass.replayNameRoom config (caller done q) operations := by
  have initial := initialize_buffers done q
  have localCode := continue_buffers q
  change 7 < 65536 ∧ (advanceCode q).code.memBound + 1 < 65536 ∧ (initialCode done q).code.memBound + 1 < 65536
  omega

private def store (g pk : Word 16) (managed live : Signing.Table Nat (ZMod 7) (Word 16))
    (saved remaining : List (Schnorr.TapeCell (ZMod 7))) : Store := (((g, pk), managed, live), saved, remaining)


private theorem hw : 16 < 2 ^ 16 := by decide
private abbrev W := wordRepresentation 16 (width_pos hw)
private abbrev P := WordBinary.pair 16 hw
private def op (o : BinOp) : Realizer .unit P W (fun value => o.eval value.1 value.2) := WordBinary.realizer .unit o hw
private def withConst (c : Word 16) : Realizer .unit W P (fun x => (x, c)) :=
  ByteRoute.realizer W P (fun x => (x, c)) [.slice 0 1, .literal [c]] hw ⟨by decide, trivial⟩ rfl (fun _ => rfl)
private def square : Realizer .unit W P (fun x => (x, x)) :=
  ByteRoute.realizer W P (fun x => (x, x)) [.slice 0 1, .slice 0 1] hw ⟨by decide, by decide, trivial⟩ rfl (fun _ => rfl)
private def project (i : Nat) (small : i < 2) : Realizer .unit P W (fun x => if i = 0 then x.1 else x.2) :=
  ByteRoute.realizer P W _ [.slice i 1] hw ⟨by change i + 1 ≤ 2; omega, trivial⟩ rfl
    (by intro x; rcases x with ⟨a, b⟩; interval_cases i <;> rfl)
private def reduce : Realizer .unit W W (fun x => x % 7) :=
  (withConst 7).then (op .umod)
/-- `(a - b) mod 7` on represented indices: wrapping word subtraction, add 7, reduce. -/
private def subWord : Realizer .unit P W (fun x => ((x.1 - x.2) + 7) % 7) :=
  ((op .sub).then (withConst 7)).then ((op .add).then reduce)
private theorem inv_seven (b : ZMod 7) : b⁻¹ = b ^ 5 := by
  by_cases zero : b = 0
  · subst zero; simp
  · apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ']
    exact ZMod.pow_card_sub_one_eq_one zero
private def fourth : Realizer .unit W W (fun x => (x * x % 7) * (x * x % 7)) :=
  ((square.then (op .mul)).then reduce).then (square.then (op .mul))
/-- `a * b⁵ mod 7 = a / b` in `ZMod 7` (including `b = 0`), on represented indices. -/
private def divWord : Realizer .unit P W (fun x => (x.1 * x.2 * ((x.2 * x.2 % 7) * (x.2 * x.2 % 7))) % 7) :=
  ((Pairing.realizer (op .mul) ((project 1 (by decide)).then fourth) (by decide) hw (by decide) (by decide)
    (by decide) (by decide) (by decide)).then (op .mul)).then reduce
private def indices (value : config.handler.core.arithmetic.scalars.Value) : Word 16 × Word 16 :=
  (BitVec.ofNat 16 value.val.1.val, BitVec.ofNat 16 value.val.2.val)
private theorem indices_bytes : ∀ value, P.encoding.encode (indices value) =
    config.handler.core.arithmetic.scalars.representation.encoding.encode value := by
  rintro ⟨⟨a, b⟩, ⟨⟩, ⟨⟩⟩; revert a b; decide
private def scalarSub : Implementation .unit config.handler.core.arithmetic.scalars config.handler.core.scalar
    (fun value => value.1 - value.2) where
  preserves _ _ := trivial
  program := (subWord.viewInput _ indices indices_bytes).viewOutput _ _ (by
    rintro ⟨⟨a, b⟩, ⟨⟩, ⟨⟩⟩; revert a b; decide)
private def scalarDivide : Implementation .unit config.handler.core.arithmetic.scalars config.handler.core.scalar
    (fun value => value.1 / value.2) where
  preserves _ _ := trivial
  program := (divWord.viewInput _ indices indices_bytes).viewOutput _ _ (by
    rintro ⟨⟨a, b⟩, ⟨⟩, ⟨⟩⟩
    show config.handler.core.scalar.representation.encoding.encode ⟨a / b, trivial⟩ = _
    rw [div_eq_mul_inv, inv_seven]
    revert a b; decide)

private def arith : ReplayFork.Extract.Arithmetic config where
  sub := scalarSub
  divide := scalarDivide
  slots := 3
  subNames := ⟨by decide, by decide⟩
  divideNames := ⟨by decide, by decide⟩
  reserve := by decide
private def arithBudget : ReplayFork.Extract.Arithmetic.Budget config arith where
  subTime := 48
  subWords := 207
  divideTime := 262
  divideWords := 1096
  sub := ⟨fun _ => le_rfl, by decide +kernel⟩
  divide := ⟨fun _ => le_rfl, by decide +kernel⟩

example : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit (ReplayFork.output config)
    config.handler.sampler.tape.scalar.representation (ReplayFork.Extract.source config) (ReplayFork.Extract.code config arith) :=
  ReplayFork.Extract.refines config arith
example : ((ReplayFork.Extract.code config arith).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  ReplayFork.Extract.descriptionFits config arith
example (qH : Fin 65535) (done : Bool) (q : CallerPackets.Request config) (fuel : Nat) :
    ((ReplayFork.Extract.fullProgram config (caller done q) operations qH.val (by have := qH.isLt; omega) arith fuel).lower
      (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  ReplayFork.Extract.full_descriptionFits config (caller done q) operations qH.val (by have := qH.isLt; omega) arith (nameRoom done q) fuel

private def prepared (value : ReplayFork.Result config) : State 16 :=
  let initial := (ReplayFork.output config).initial value
  { initial with bufs := fun i => if i = 200 then #[77] else initial.bufs i
                 caps := fun i => if i = 200 then 4 else initial.caps i
                 regs := fun i => if i = 99 then 91 else initial.regs i
                 tapePos := 9 }

/-- Run the executed extractor on a represented controller result. -/
private def runExtract (value : ReplayFork.Result config) (replies : List (Word 16)) := do
  let body := ReplayFork.Extract.code config arith
  let result ← WordIO.run .unit RandomTape.zero 1000000 (body.lower (Fresh.port config.handler.sampler.tape)) (prepared value) replies
  pure (((config.handler.sampler.tape.scalar.representation.encoding.decode (result.state.bufs 0).toList).map
      (fun answer : config.handler.sampler.tape.scalar.Value => answer.val)),
    result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
    result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ ReplayFork.Extract.timeBudget config arith arithBudget))

/-- Run the complete solver: initialized fork controller, then the extractor. -/
private def runFull (qH : Fin 65535) (done : Bool) (q : CallerPackets.Request config)
    (fuel : Fin 2) (g pk : Word 16) (replies : List (Word 16)) := do
  let value : (Pass.Initialization.points config).Value := ⟨(g, pk), trivial, trivial⟩
  let initial := (ReplayFork.Setup.input config).initial value
  let before := { initial with bufs := fun i => if i = 200 then #[77] else initial.bufs i
                               caps := fun i => if i = 200 then 4 else initial.caps i
                               regs := fun i => if i = 99 then 91 else initial.regs i
                               tapePos := 9 }
  let body := ReplayFork.Extract.fullProgram config (caller done q) operations qH.val (by have := qH.isLt; omega) arith fuel.val
  let result ← WordIO.run .unit RandomTape.zero 1000000 (body.lower (Fresh.port config.handler.sampler.tape)) before replies
  pure (((config.handler.sampler.tape.scalar.representation.encoding.decode (result.state.bufs 0).toList).map
      (fun answer : config.handler.sampler.tape.scalar.Value => answer.val)),
    result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
    result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ ReplayFork.Extract.fullTimeBudget config (caller done q) operations qH.val
      (by have := qH.isLt; omega) budget (localBudget done q) arith arithBudget fuel.val))

private def pass (commitment : Word 16) (response challenge : ZMod 7) : Terminal.Output config :=
  (.inr (⟨(2, commitment, response), by change 2 < 256; decide, trivial, trivial⟩, ⟨challenge, trivial⟩),
    ⟨store 3 5 [] [] [] [], by decide⟩)
private def cutoff : Terminal.Output config :=
  (.inl (), ⟨store 3 5 [] [] [] [], by decide⟩)

open Lean in
run_cmd do
  let draw (k : Word 16) : List (WordIO.Event 16) := [.output 6, .invoke, .input 6, .input k]
  -- Failure tag: one fresh reply is consumed and its uniform index returned.
  for k in [(0 : Word 16), 1, 3, 6] do
    unless runExtract (.inl ()) [6, k, 88] ==
        some (some (BitVec.toNat k % 7 : ZMod 7), draw k, [88], #[77], 4, 91, 9, true, true) do
      throwError "failure tag must draw uniformly from one fresh reply"
  -- Successful fork, equal commitments, distinct challenges: the exact quotient, no reply.
  unless runExtract (.inr (pass 9 6 4, pass 9 1 2)) [6, 3, 88] ==
      some (some 6, [], [6, 3, 88], #[77], 4, 91, 9, true, true) do
    throwError "successful fork must return (6 - 1) / (4 - 2) = 6 without sampling"
  for (z₁, z₂, c₁, c₂) in [((0 : ZMod 7), (0 : ZMod 7), (4 : ZMod 7), (5 : ZMod 7)), (3, 5, 0, 6), (6, 2, 1, 3), (1, 1, 5, 2)] do
    unless runExtract (.inr (pass 2 z₁ c₁, pass 2 z₂ c₂)) [6, 3, 88] ==
        some (some ((z₁ - z₂) / (c₁ - c₂)), [], [6, 3, 88], #[77], 4, 91, 9, true, true) do
      throwError "successful fork lost the exact field quotient"
  -- Equal challenges, different commitments, or a cutoff pass fall back to the uniform draw.
  unless runExtract (.inr (pass 9 6 4, pass 9 1 4)) [6, 5, 88] ==
      some (some 5, draw 5, [88], #[77], 4, 91, 9, true, true) do
    throwError "equal challenges must fall back to the uniform draw"
  unless runExtract (.inr (pass 9 6 4, pass 8 1 2)) [6, 2, 88] ==
      some (some 2, draw 2, [88], #[77], 4, 91, 9, true, true) do
    throwError "different commitments must fall back to the uniform draw"
  unless runExtract (.inr (cutoff, pass 9 1 2)) [6, 1, 88] ==
      some (some 1, draw 1, [88], #[77], 4, 91, 9, true, true) &&
      runExtract (.inr (pass 9 6 4, cutoff)) [6, 1, 88] ==
      some (some 1, draw 1, [88], #[77], 4, 91, 9, true, true) do
    throwError "a cutoff pass inside a successful fork tag must fall back to the uniform draw"
  unless runExtract (.inl ()) [6] == none do
    throwError "fallback admitted an incomplete reply"
  -- Complete solver: the initialized controller followed by the extractor.
  unless runFull 0 true random 0 3 0 [6, 4, 6, 5, 88] ==
      some (some 0, [.output 6, .invoke, .input 6, .input 4, .output 6, .invoke, .input 6, .input 5], [88],
        #[77], 4, 91, 9, true, true) do
    throwError "full solver must extract from a successful fork without a further reply"
  unless runFull 0 false random 0 3 0 [6, 4, 6, 5, 88] ==
      some (some 4, draw 4, [6, 5, 88], #[77], 4, 91, 9, true, true) do
    throwError "full solver must draw uniformly after a cutoff fork"
  unless runFull 0 true random 0 3 0 [6, 4, 6, 4, 6, 2, 88] ==
      some (some 2, [.output 6, .invoke, .input 6, .input 4, .output 6, .invoke, .input 6, .input 4] ++ draw 2, [88],
        #[77], 4, 91, 9, true, true) do
    throwError "full solver must draw uniformly after a duplicate-challenge fork"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``ReplayFork.Extract.headersRoute, ``ReplayFork.Extract.gather, ``ReplayFork.Extract.core,
      ``ReplayFork.Extract.classifier, ``ReplayFork.Extract.dispatched_value, ``ReplayFork.Extract.select_refines,
      ``ReplayFork.Extract.refines, ``ReplayFork.Extract.observe, ``ReplayFork.Extract.finish_fallback,
      ``ReplayFork.Extract.source_original, ``ReplayFork.Extract.full_refines, ``ReplayFork.Extract.sample_liftRandom,
      ``ReplayFork.Extract.fullSource_original, ``ReplayFork.Extract.full_observe_original,
      ``ReplayFork.Extract.core_bounded, ``ReplayFork.Extract.core_buffers, ``ReplayFork.Extract.core_names,
      ``ReplayFork.Extract.classifier_bounded, ``ReplayFork.Extract.classifier_names, ``ReplayFork.Extract.classifier_buffers,
      ``ReplayFork.Extract.select_time, ``ReplayFork.Extract.select_words, ``ReplayFork.Extract.select_buffers,
      ``ReplayFork.Extract.select_names, ``ReplayFork.Extract.select_descriptionFits,
      ``ReplayFork.Extract.time, ``ReplayFork.Extract.words, ``ReplayFork.Extract.names, ``ReplayFork.Extract.buffers,
      ``ReplayFork.Extract.descriptionFits, ``ReplayFork.Extract.resources,
      ``ReplayFork.Extract.full_time, ``ReplayFork.Extract.full_words, ``ReplayFork.Extract.full_names,
      ``ReplayFork.Extract.full_buffers, ``ReplayFork.Extract.full_descriptionFits, ``ReplayFork.Extract.full_resources] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMReplayExtract
