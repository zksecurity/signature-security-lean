import Signatures.Runtime.Caliper.SchnorrROMNonzeroSigningHandlerBounds
import Signatures.Runtime.Caliper.SchnorrROMNonzeroSigningBranch
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMNonzeroSigning
open SchnorrROMTape SchnorrROM

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance : SMul (ZMod 7) (Word 16) := ⟨fun scalar point => BitVec.ofNat 16 scalar.val * point⟩
private def params : PrivateSampler.Enumerated.Parameters 16 (ZMod 7) :=
  PrivateSampler.Enumerated.Parameters.ofFinEnum 16 (ZMod 7) 6 (by decide) (by decide) (by decide)
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

private theorem hw : 16 < 2 ^ 16 := by decide
private abbrev W := wordRepresentation 16 (width_pos hw)
private abbrev P := WordBinary.pair 16 hw
private def op (o : BinOp) : Realizer .unit P W (fun value => o.eval value.1 value.2) := WordBinary.realizer .unit o hw
private def withConst (c : Word 16) : Realizer .unit W P (fun x => (x, c)) :=
  ByteRoute.realizer W P (fun x => (x, c)) [.slice 0 1, .literal [c]] hw ⟨by decide, trivial⟩ rfl (fun _ => rfl)
/-- `(a + b) mod 7` on represented indices: word addition, then reduction. -/
private def addWord : Realizer .unit P W (fun x => (x.1 + x.2) % 7) :=
  (op .add).then ((withConst 7).then (op .umod))
private def indices (value : config.handler.core.arithmetic.scalars.Value) : Word 16 × Word 16 :=
  (BitVec.ofNat 16 value.val.1.val, BitVec.ofNat 16 value.val.2.val)
private theorem indices_bytes : ∀ value, P.encoding.encode (indices value) =
    config.handler.core.arithmetic.scalars.representation.encoding.encode value := by
  rintro ⟨⟨a, b⟩, ⟨⟩, ⟨⟩⟩; revert a b; decide
private def scalarAdd : Implementation .unit config.handler.core.arithmetic.scalars config.handler.core.scalar
    (fun value => value.1 + value.2) where
  preserves _ _ := trivial
  program := (addWord.viewInput _ indices indices_bytes).viewOutput _ _ (by
    rintro ⟨⟨a, b⟩, ⟨⟩, ⟨⟩⟩; revert a b; decide)
private def arith : SchnorrROM.NonzeroSigning.Arithmetic config where
  add := scalarAdd
  slots := 3
  addNames := ⟨by decide, by decide⟩
  reserve := by decide

private theorem positive : 0 < config.sampler.bound := by decide
private theorem addBound : scalarAdd.BoundedBy 27 117 := ⟨fun _ => le_rfl, by decide +kernel⟩

/-! ### The direct nonzero draw -/

open PrivateSampler.Enumerated in
private theorem nonzero_law :
    letI := Nonzero.unitsSampleable params
    Subtype.val <$> Nonzero.Direct.nonzeroSource params (Nonzero.bound_pos params) =
      (fun a : (ZMod 7)ˣ => (a : ZMod 7)) <$> ($ᵗ (ZMod 7)ˣ : ProbComp (ZMod 7)ˣ) :=
  Nonzero.Direct.uniform params

private def runDirect (replies : List (Word 16)) := do
  let program := PrivateSampler.Enumerated.Nonzero.Direct.code params positive
  let initial := (PrivateSampler.Enumerated.tape params).unit.representation.initial ⟨(), trivial⟩
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 100000 (program.lower (Fresh.port (PrivateSampler.Enumerated.tape params)))
    before replies
  pure (((PrivateSampler.Enumerated.scalar params).representation.encoding.decode (result.state.bufs 0).toList).map
      (fun value : (PrivateSampler.Enumerated.scalar params).Value => value.val),
    result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
    result.state.tapePos, (List.range 20).all (fun i => result.state.caps (i + 1) == 0), decide (result.time ≤ 180))

/-! ### The executed signing branch -/

private def program := NonzeroSigning.code config operations arith positive
private theorem bounded : Interactive.TimeBoundOn (NonzeroSigning.ready config) (Fresh.port config.handler.sampler.tape) .unit
    config.handler.input.representation program (NonzeroSigning.handlerTime config 6 6 27) :=
  NonzeroSigning.time_bound config operations arith positive scaleBound subBound addBound
private theorem stored : (program.lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    NonzeroSigning.handlerWords config positive 27 27 117 :=
  NonzeroSigning.code_bound config operations arith positive scaleBound subBound addBound
private theorem named : WordIO.NamesAccounted (program.lower (Fresh.port config.handler.sampler.tape))
    (NonzeroSigning.handlerNames config 3) :=
  NonzeroSigning.handler_names config operations arith positive 3 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩
private theorem accepted : (program.lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  NonzeroSigning.descriptionFits config operations arith positive
private theorem bufferBound : (program.lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 11 :=
  (NonzeroSigning.handler_buffers config operations arith positive).trans (by decide)
private instance (value : Nat × Schnorr.ListROM.Shared.Store (ZMod 7) (Word 16) Nat) : Decidable (config.handler.input.valid value) := by
  change Decidable ((value.1 < 256 ∧
    (((True ∧ True) ∧ (value.2.1.2.1.length ≤ 3 ∧ ∀ entry ∈ value.2.1.2.1, (entry.1.1 < 256 ∧ True) ∧ True) ∧
      (value.2.1.2.2.length ≤ 3 ∧ ∀ entry ∈ value.2.1.2.2, (entry.1.1 < 256 ∧ True) ∧ True)) ∧
      (value.2.2.1.length ≤ 6 ∧ ∀ cell ∈ value.2.2.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
      (value.2.2.2.length ≤ 6 ∧ ∀ cell ∈ value.2.2.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536))) ∧
    value.2.1.2.1.length ≤ 2)
  infer_instance

private def saved : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 1)]
private def live : Signing.Table Nat (ZMod 7) (Word 16) := [((7, 11), 0), ((8, 9), 4)]
private def managed : Signing.Table Nat (ZMod 7) (Word 16) := [((5, 6), 1)]
private def run (g pk : Word 16) (message : Nat) (cache : Signing.Table Nat (ZMod 7) (Word 16))
    (remaining : List (Schnorr.TapeCell (ZMod 7))) (replies : List (Word 16)) := do
  let raw := (message, ((g, pk), cache, live), saved, remaining)
  let input : config.handler.input.Value ← if valid : config.handler.input.valid raw then some ⟨raw, valid⟩ else none
  let initial := config.handler.input.representation.initial input
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 1000000 (program.lower (Fresh.port config.handler.sampler.tape)) before replies
  let decoded := (config.handler.output.representation.encoding.decode (result.state.bufs 0).toList).map Subtype.val
  pure (decoded, result.trace, result.remaining, result.state.bufs 200, result.state.caps 200,
    result.state.regs 99, result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ NonzeroSigning.handlerTime config 6 6 27))

open Lean in
run_cmd do
  -- The direct nonzero draw: one uniform reply below `bound = 6`, mapped past the zero index.
  for k in [(0 : Word 16), 1, 2, 3, 4, 5] do
    let expected : ZMod 7 := (k.toNat + 1 : Nat)
    unless runDirect [5, k, 88] ==
        some (some expected, [.output 5, .invoke, .input 5, .input k], [88], #[77], 4, 91, 9, true, true) do
      throwError "direct nonzero draw changed its range, result, trace or external state"
  let hits := ([(0 : Word 16), 1, 2, 3, 4, 5].filterMap fun k =>
    (runDirect [5, k, 88]).bind fun result => result.1)
  unless hits.all (· ≠ 0) && ([1, 2, 3, 4, 5, 6] : List (ZMod 7)).all (· ∈ hits) do
    throwError "direct nonzero draw returned zero or missed a nonzero residue"
  unless runDirect [5] == none do throwError "direct nonzero draw returned without its reply"
  let tail : List (Schnorr.TapeCell (ZMod 7)) := [(1, 4, 0)]
  -- R = 6 • 3 - 3 • 5 = 3 ≠ 0: the plain transcript, cache programmed at (msg, R).
  unless run 3 5 7 managed ([(8, 0, 3), (8, 0, 6), (7, 0, 2)] ++ tail) [88] ==
      some (some ((3, 6), ((3, 5), [((7, 3), 3), ((5, 6), 1)], live), saved, tail), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "nonzero commitment did not return (R, z), program the cache, or preserve LIVE and the tapes"
  -- R = 5 • 3 - 3 • 5 = 0: the repair (a • g, z + a) with a = 3.
  unless run 3 5 7 managed ([(8, 0, 3), (8, 0, 5), (7, 0, 2)] ++ tail) [88] ==
      some (some ((9, 1), ((3, 5), [((7, 9), 3), ((5, 6), 1)], live), saved, tail), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "zero commitment did not take the repair branch"
  -- g = pk = 0 forces R = 0 for every draw; the repaired response is z + a.
  for (c, z, k) in [((0 : Nat), (4 : Nat), (5 : Nat)), (2, 6, 0), (5, 0, 3)] do
    unless run 0 0 9 [] ([(8, 0, c), (8, 0, z), (7, 0, k)] ++ tail) [88] ==
        some (some ((0, ((z + k + 1 : Nat) : ZMod 7)), ((0, 0), [((9, 0), (c : ZMod 7))], live), saved, tail), [], [88],
          #[77], 4, 91, 9, true, true) do
      throwError "forced zero commitment lost the repaired response"
  -- A cached key is never overwritten.
  let cached : Signing.Table Nat (ZMod 7) (Word 16) := [((7, 3), 5)]
  unless run 3 5 7 cached ([(8, 0, 3), (8, 0, 6), (7, 0, 2)] ++ tail) [88] ==
      some (some ((3, 6), ((3, 5), cached, live), saved, tail), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "signing overwrote a programmed cache entry"
  -- Fresh draws: three replies appended to the shared tape in order.
  unless run 3 5 7 managed tail [6, 3, 6, 5, 5, 2, 88] ==
      some (some ((9, 1), ((3, 5), [((7, 9), 3), ((5, 6), 1)], live), saved ++ [(8, 0, 3), (8, 0, 5), (7, 0, 2)], tail),
        [.output 6, .invoke, .input 6, .input 3, .output 6, .invoke, .input 6, .input 5,
         .output 5, .invoke, .input 5, .input 2], [88], #[77], 4, 91, 9, true, true) do
    throwError "fresh signing draws were not recorded on the shared tape in order"
  unless run 3 5 7 managed ([(8, 0, 3), (8, 0, 6)] ++ tail) [5, 4, 88] ==
      some (some ((3, 6), ((3, 5), [((7, 3), 3), ((5, 6), 1)], live), saved ++ [(7, 0, 4)], tail),
        [.output 5, .invoke, .input 5, .input 4], [88], #[77], 4, 91, 9, true, true) do
    throwError "the nonce draw lost the replay/fresh boundary"
  unless run 3 5 7 managed tail [6, 3, 6, 5] == none do throwError "signing succeeded without its nonce reply"
  unless run 256 0 0 managed tail [] == none do throwError "unrepresented message was admitted"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``PrivateSampler.Enumerated.Nonzero.caller, ``PrivateSampler.Enumerated.Nonzero.terminates,
      ``PrivateSampler.Enumerated.Nonzero.original_typed, ``PrivateSampler.Enumerated.Nonzero.Direct.refines,
      ``PrivateSampler.Enumerated.Nonzero.Direct.uniform, ``PrivateSampler.Enumerated.Nonzero.samples,
      ``PrivateSampler.Enumerated.Nonzero.Direct.nonzero, ``PrivateSampler.Enumerated.Nonzero.Direct.within,
      ``PrivateSampler.Enumerated.Nonzero.Direct.time_bound, ``PrivateSampler.Enumerated.Nonzero.Direct.code_words,
      ``PrivateSampler.Enumerated.Nonzero.Direct.names, ``PrivateSampler.Enumerated.Nonzero.Direct.buffers,
      ``PrivateSampler.Enumerated.Nonzero.Direct.descriptionFits,
      ``PrivateSampler.Enumerated.Nonzero.continuation_time, ``PrivateSampler.Enumerated.Nonzero.continuation_words,
      ``PrivateSampler.Enumerated.Nonzero.continuation_names,
      ``NonzeroSigning.implementation, ``NonzeroSigning.bounded, ``NonzeroSigning.names, ``NonzeroSigning.buffers,
      ``NonzeroSigning.resources, ``NonzeroSigning.code, ``NonzeroSigning.refines, ``NonzeroSigning.preserves_live,
      ``NonzeroSigning.managed_length, ``NonzeroSigning.reserved_after, ``NonzeroSigning.source_eq,
      ``NonzeroSigning.source_original, ``NonzeroSigning.observe_original,
      ``NonzeroSigning.time_bound, ``NonzeroSigning.code_bound, ``NonzeroSigning.handler_names,
      ``NonzeroSigning.handler_buffers, ``NonzeroSigning.descriptionFits, ``NonzeroSigning.handler_resources,
      ``nonzero_law, ``addBound, ``bounded, ``stored, ``named, ``accepted, ``bufferBound] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

/-! ### The branch as a handler component -/

/-- The nonzero-nonce branch assembled into a complete handler operation record;
its source law `Handler.nonzeroLaw` needs a genuine module structure on the group,
which this word-arithmetic fixture does not have. -/
private def nonzeroOperations : Handler.Operations config :=
  Handler.withNonzero config operations arith positive scaleBound subBound addBound (by
    change max 3 3 + 1 + 3 < 2 ^ 16; decide)
end SignaturesTest.CaliperSchnorrROMNonzeroSigning
