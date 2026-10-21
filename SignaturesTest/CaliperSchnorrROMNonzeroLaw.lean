import Signatures.Runtime.Caliper.SchnorrROMNonzeroSigningBranch
import Lean

/-! A concrete nonzero-nonce handler on an actual module: points are `ZMod 7`
itself, with executed mod-7 scaling, subtraction and field addition, so
`Handler.nonzeroLaw` instantiates and the whole handler's source is the
nonzero-nonce list backend. -/

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMNonzeroLaw
open SchnorrROMTape SchnorrROM

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def params : PrivateSampler.Enumerated.Parameters 16 (ZMod 7) :=
  PrivateSampler.Enumerated.Parameters.ofFinEnum 16 (ZMod 7) 12 (by decide) (by decide) (by decide)
private def config : Signing.Enumerated.Configuration 16 Nat (ZMod 7) (ZMod 7) where
  sampler := params
  message := Layout.counter 16 256 (by decide) (by decide)
  point := PrivateSampler.Enumerated.scalar params
  capacityPred := 2
  countFits := by decide
  storageFits := by decide

private theorem hw : 16 < 2 ^ 16 := by decide
private abbrev W := wordRepresentation 16 (width_pos hw)
private abbrev P := WordBinary.pair 16 hw
private def op (o : BinOp) : Realizer .unit P W (fun value => o.eval value.1 value.2) := WordBinary.realizer .unit o hw
private def withConst (c : Word 16) : Realizer .unit W P (fun x => (x, c)) :=
  ByteRoute.realizer W P (fun x => (x, c)) [.slice 0 1, .literal [c]] hw ⟨by decide, trivial⟩ rfl (fun _ => rfl)
private def reduce : Realizer .unit W W (fun x => x % 7) := (withConst 7).then (op .umod)
private def mulWord : Realizer .unit P W (fun x => x.1 * x.2 % 7) := (op .mul).then reduce
private def subWord : Realizer .unit P W (fun x => ((x.1 - x.2) + 7) % 7) :=
  ((op .sub).then (withConst 7)).then ((op .add).then reduce)
private def addWord : Realizer .unit P W (fun x => (x.1 + x.2) % 7) := (op .add).then reduce
private def scaleIndices (value : config.handler.core.arithmetic.scaleArgs.Value) : Word 16 × Word 16 :=
  (BitVec.ofNat 16 value.val.1.val, BitVec.ofNat 16 value.val.2.val)
private def pointIndices (value : config.handler.core.arithmetic.points.Value) : Word 16 × Word 16 :=
  (BitVec.ofNat 16 value.val.1.val, BitVec.ofNat 16 value.val.2.val)
private def scalarIndices (value : config.handler.core.arithmetic.scalars.Value) : Word 16 × Word 16 :=
  (BitVec.ofNat 16 value.val.1.val, BitVec.ofNat 16 value.val.2.val)
private def scale : Implementation .unit config.handler.core.arithmetic.scaleArgs config.handler.core.point
    (fun value => value.1 • value.2) where
  preserves _ _ := trivial
  program := (mulWord.viewInput _ scaleIndices (by rintro ⟨⟨a, b⟩, ⟨⟩, ⟨⟩⟩; revert a b; decide)).viewOutput _ _ (by
    rintro ⟨⟨a, b⟩, ⟨⟩, ⟨⟩⟩; revert a b; decide)
private def sub : Implementation .unit config.handler.core.arithmetic.points config.handler.core.point
    (fun value => value.1 - value.2) where
  preserves _ _ := trivial
  program := (subWord.viewInput _ pointIndices (by rintro ⟨⟨a, b⟩, ⟨⟩, ⟨⟩⟩; revert a b; decide)).viewOutput _ _ (by
    rintro ⟨⟨a, b⟩, ⟨⟩, ⟨⟩⟩; revert a b; decide)
private def scalarAdd : Implementation .unit config.handler.core.arithmetic.scalars config.handler.core.scalar
    (fun value => value.1 + value.2) where
  preserves _ _ := trivial
  program := (addWord.viewInput _ scalarIndices (by rintro ⟨⟨a, b⟩, ⟨⟩, ⟨⟩⟩; revert a b; decide)).viewOutput _ _ (by
    rintro ⟨⟨a, b⟩, ⟨⟩, ⟨⟩⟩; revert a b; decide)
private theorem scaleBound : scale.BoundedBy 27 117 := ⟨fun _ => le_rfl, by decide +kernel⟩
private theorem subBound : sub.BoundedBy 48 207 := ⟨fun _ => le_rfl, by decide +kernel⟩
private theorem addBound : scalarAdd.BoundedBy 27 117 := ⟨fun _ => le_rfl, by decide +kernel⟩
private theorem positive : 0 < config.sampler.bound := by decide

private def base : Handler.Operations config where
  scale := scale
  sub := sub
  slots := 3
  scaleNames := ⟨by decide, by decide⟩
  subNames := ⟨by decide, by decide⟩
  reserve := by decide
  signing := Handler.fullField config scale sub ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) scaleBound subBound
private def arith : NonzeroSigning.Arithmetic config where
  add := scalarAdd
  slots := 3
  addNames := ⟨by decide, by decide⟩
  reserve := by decide
private def operations : Handler.Operations config :=
  Handler.withNonzero config base arith positive scaleBound subBound addBound (by change max 3 3 + 1 + 3 < 2 ^ 16; decide)
private def law : Handler.SigningLaw config operations.signing :=
  Handler.nonzeroLaw config base arith positive scaleBound subBound addBound

/-- The law's target is the nonzero-nonce list backend, as `Parameters.Nonzero` demands. -/
example :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    letI := PrivateSampler.Enumerated.Nonzero.unitsSampleable config.sampler
    law.target = Schnorr.NonzeroListROM.handler (G₂ := ZMod 7) (K := Nat) := rfl

/-- The whole executed handler's source is the nonzero-nonce backend, stated with
the repository's original FinEnum field sampler. -/
private theorem handler_original (value : Handler.Input config) (valid : Handler.ready config value) :
    letI := PrivateSampler.Enumerated.Nonzero.unitsSampleable config.sampler
    Handler.observed config <$> Handler.source config operations value =
      (fun answer => (Handler.representReply config value answer.1, answer.2)) <$>
        (Schnorr.ListROM.Shared.interpret (Schnorr.NonzeroListROM.handler (G₂ := ZMod 7) (K := Nat)
          (Handler.query config value))).run (Handler.initialStore config value) := by
  have same : PrivateSampler.Enumerated.sampleable config.sampler = FinEnum.SampleableType (ZMod 7) :=
    PrivateSampler.Enumerated.sampleable_finEnum 12 (by decide) (by decide) (by decide)
  have original := Handler.source_original config operations law value valid
  rw [same] at original
  exact original

/-! ### Executing the signing branch on the module -/

private def program := operations.signing.code
private instance (value : Nat × Schnorr.ListROM.Shared.Store (ZMod 7) (ZMod 7) Nat) : Decidable (config.handler.input.valid value) := by
  change Decidable ((value.1 < 256 ∧
    (((True ∧ True) ∧ (value.2.1.2.1.length ≤ 3 ∧ ∀ entry ∈ value.2.1.2.1, (entry.1.1 < 256 ∧ True) ∧ True) ∧
      (value.2.1.2.2.length ≤ 3 ∧ ∀ entry ∈ value.2.1.2.2, (entry.1.1 < 256 ∧ True) ∧ True)) ∧
      (value.2.2.1.length ≤ 12 ∧ ∀ cell ∈ value.2.2.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
      (value.2.2.2.length ≤ 12 ∧ ∀ cell ∈ value.2.2.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536))) ∧
    value.2.1.2.1.length ≤ 2)
  infer_instance

private def saved : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 1)]
private def live : Signing.Table Nat (ZMod 7) (ZMod 7) := [((7, 4), 0), ((8, 2), 4)]
private def managed : Signing.Table Nat (ZMod 7) (ZMod 7) := [((5, 6), 1)]
private def run (g pk : ZMod 7) (message : Nat) (cache : Signing.Table Nat (ZMod 7) (ZMod 7))
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
    decide (result.time ≤ operations.signing.time))

open Lean in
run_cmd do
  let tail : List (Schnorr.TapeCell (ZMod 7)) := [(1, 4, 0)]
  -- g = 3, pk = 5, c = 3, z = 6: R = 6·3 − 3·5 = 3 ≠ 0, so (R, z) and the cache is programmed at (msg, R).
  unless run 3 5 7 managed ([(8, 0, 3), (8, 0, 6), (7, 0, 2)] ++ tail) [88] ==
      some (some ((3, 6), ((3, 5), [((7, 3), 3), ((5, 6), 1)], live), saved, tail), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "nonzero commitment did not return (R, z), program the cache, or preserve LIVE and the tapes"
  -- c = 1, z = 4: R = 4·3 − 1·5 = 7 = 0 in ZMod 7; the repair with a = 3 gives (a·g, z + a) = (2, 0).
  unless run 3 5 7 managed ([(8, 0, 1), (8, 0, 4), (7, 0, 2)] ++ tail) [88] ==
      some (some ((2, 0), ((3, 5), [((7, 2), 1), ((5, 6), 1)], live), saved, tail), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "zero commitment did not take the repair branch"
  -- g = pk = 0 forces R = 0 for every draw; the repaired response is z + a.
  for (c, z, k) in [((0 : Nat), (4 : Nat), (5 : Nat)), (2, 6, 0), (5, 0, 3)] do
    unless run 0 0 9 [] ([(8, 0, c), (8, 0, z), (7, 0, k)] ++ tail) [88] ==
        some (some ((0, ((z + k + 1 : Nat) : ZMod 7)), ((0, 0), [((9, 0), (c : ZMod 7))], live), saved, tail), [], [88],
          #[77], 4, 91, 9, true, true) do
      throwError "forced zero commitment lost the repaired response"
  -- Fresh draws: three replies appended to the shared tape in order.
  unless run 3 5 7 managed tail [6, 1, 6, 4, 5, 2, 88] ==
      some (some ((2, 0), ((3, 5), [((7, 2), 1), ((5, 6), 1)], live), saved ++ [(8, 0, 1), (8, 0, 4), (7, 0, 2)], tail),
        [.output 6, .invoke, .input 6, .input 1, .output 6, .invoke, .input 6, .input 4,
         .output 5, .invoke, .input 5, .input 2], [88], #[77], 4, 91, 9, true, true) do
    throwError "fresh signing draws were not recorded on the shared tape in order"
  unless run 3 5 7 managed tail [6, 1, 6, 4] == none do throwError "signing succeeded without its nonce reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``law, ``operations, ``handler_original, ``scaleBound, ``subBound, ``addBound] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMNonzeroLaw
