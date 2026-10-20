import Signatures.Runtime.Caliper.SchnorrROMCallerMemory
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMCaller
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
private def operations : Handler.Operations config where
  scale := scale
  sub := sub
  slots := 3
  scaleNames := ⟨by decide, by decide⟩
  subNames := ⟨by decide, by decide⟩
  reserve := by decide
private def budget : Handler.Budget config operations where
  scaleTime := 6
  scaleWords := 27
  subTime := 6
  subWords := 27
  scale := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
  sub := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩

private abbrev Store := Schnorr.ListROM.Shared.Store (ZMod 7) (Word 16) Nat
private abbrev Query := (Nat ⊕ (Nat × Word 16)) ⊕ Nat
private instance (value : Store) : Decidable (config.handler.store.valid value) := by
  change Decidable ((((True ∧ True) ∧
    (value.1.2.1.length ≤ 3 ∧ ∀ entry ∈ value.1.2.1, (entry.1.1 < 256 ∧ True) ∧ True) ∧
    (value.1.2.2.length ≤ 3 ∧ ∀ entry ∈ value.1.2.2, (entry.1.1 < 256 ∧ True) ∧ True)) ∧
    (value.2.1.length ≤ 6 ∧ ∀ cell ∈ value.2.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
    (value.2.2.length ≤ 6 ∧ ∀ cell ∈ value.2.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536)))
  infer_instance
private def packet (query : Query) (saved : Store) : Option (CallerPackets.Packet config) := do
  if good : config.handler.store.valid saved then
    match query with
    | .inl (.inl range) =>
      if bound : range < 65534 then some (.inl (.inl ⟨range, bound⟩), ⟨saved, good⟩) else none
    | .inl (.inr key) =>
      if bound : key.1 < 256 then some (.inl (.inr ⟨key, bound, trivial⟩), ⟨saved, good⟩) else none
    | .inr message =>
      if bound : message < 256 then some (.inr ⟨message, bound⟩, ⟨saved, good⟩) else none
  else none

private def run (query : Query) (saved : Store) (replies : List (Word 16)) := do
  let value ← packet query saved
  if !(decide (CallerPackets.ready config value)) then none else do
    let initial := (CallerPackets.input config).initial value
    let before := { initial with
      bufs := fun b => if b = 200 then #[77] else initial.bufs b
      caps := fun b => if b = 200 then 4 else initial.caps b
      regs := fun r => if r = 99 then 91 else initial.regs r
      tapePos := 9 }
    let result ← WordIO.run .unit RandomTape.zero 1000000
      ((CallerHandler.code config operations).lower (Fresh.port config.handler.sampler.tape)) before replies
    pure (((CallerPackets.output config).encoding.decode (result.state.bufs 0).toList).map (CallerHandler.observed config),
      result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
      result.state.tapePos, (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
      decide (result.time ≤ CallerHandler.timeBudget config operations budget))

private def saved : List (Schnorr.TapeCell (ZMod 7)) := [(3, 0, 1)]
private def managed : Signing.Table Nat (ZMod 7) (Word 16) := [((5, 6), 1)]
private def live : Signing.Table Nat (ZMod 7) (Word 16) := [((7, 3), 0)]
private def store (managed live : Signing.Table Nat (ZMod 7) (Word 16))
    (saved remaining : List (Schnorr.TapeCell (ZMod 7))) : Store := (((3, 5), managed, live), saved, remaining)

-- The source correspondence also specializes to an actual field/module model
-- and the repository's original FinEnum sampling instance.
private def groupConfig : Signing.Enumerated.Configuration 16 Nat (ZMod 7) (ZMod 7) where
  sampler := params
  message := config.message
  point := PrivateSampler.Enumerated.scalar params
  capacityPred := 2
  countFits := by decide
  storageFits := by decide
private theorem matches_original (ops : Handler.Operations groupConfig) (value : CallerPackets.Packet groupConfig)
    (valid : CallerPackets.ready groupConfig value) :
    CallerHandler.observed groupConfig <$> CallerHandler.source groupConfig ops value =
      (fun answer => (CallerHandler.representReply groupConfig value.1 answer.1, answer.2)) <$>
        (Schnorr.ListROM.Shared.interpret (Schnorr.ListROM.handler (G₂ := ZMod 7) (K := Nat)
          (CallerHandler.query groupConfig value.1))).run value.2.val := by
  have same : PrivateSampler.Enumerated.sampleable groupConfig.sampler = FinEnum.SampleableType (ZMod 7) :=
    PrivateSampler.Enumerated.sampleable_finEnum 6 (by decide) (by decide) (by decide)
  have original := CallerHandler.source_original (G₂ := ZMod 7) (K := Nat) groupConfig ops value valid
  rw [same] at original
  exact original

open Lean in
run_cmd do
  let publicTape : List (Schnorr.TapeCell (ZMod 7)) := [(1, 4, 0)]
  let replay : List (Schnorr.TapeCell (ZMod 7)) := [(8, 0, 10), (8, 0, 20)] ++ publicTape
  unless run (.inl (.inl 6)) (store managed live saved replay) [88] ==
      some (some (.inl (.inl (6, 3)), store managed live saved ([(8, 0, 20)] ++ publicTape)),
        [], [88], #[77], 4, 91, 9, true, true) do
    throwError "caller random packet lost the range, replay family or retained store"
  unless run (.inl (.inl 7)) (store managed live saved publicTape) [7, 4, 88] ==
      some (some (.inl (.inl (7, 4)), store managed live (saved ++ [(9, 0, 4)]) publicTape),
        [.output 7, .invoke, .input 7, .input 4], [88], #[77], 4, 91, 9, true, true) do
    throwError "caller random packet did not record a fresh private reply"
  unless run (.inl (.inr (9, 9))) (store managed live saved replay) [88] ==
      some (some (.inl (.inr 4), store ([((9, 9), 4)] ++ managed) ([((9, 9), 4)] ++ live)
        saved [(8, 0, 10), (8, 0, 20)]), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "caller hash packet did not isolate public replay or update both caches"
  unless run (.inl (.inr (9, 9))) (store managed live saved []) [6, 0, 88] ==
      some (some (.inl (.inr 0), store ([((9, 9), 0)] ++ managed) ([((9, 9), 0)] ++ live)
        (saved ++ [(1, 0, 0)]) []), [.output 6, .invoke, .input 6, .input 0], [88], #[77], 4, 91, 9, true, true) do
    throwError "caller hash packet lost fresh public zero or used a private family"
  let programmed := [((7, (3 : Word 16)), (3 : ZMod 7))] ++ managed
  unless run (.inr 7) (store managed live saved replay) [88] ==
      some (some (.inr (3, 6), store programmed live saved publicTape), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "caller signing packet lost its signature, two ordered private draws or untouched LIVE table"
  let freshTape := saved ++ [(8, 0, 3), (8, 0, 6)]
  let signed ← match run (.inr 7) (store managed live saved publicTape) [6, 3, 6, 6, 88] with
    | some (some (.inr signature, after), trace, remaining, external, capacity, register, cursor, scratch, elapsed) =>
      unless signature == (3, 6) && remaining == [88] && external == #[77] && capacity == 4 &&
          register == 91 && cursor == 9 && scratch && elapsed do
        throwError "fresh signing lost its output, external state or resource bounds"
      unless trace == [.output 6, .invoke, .input 6, .input 3, .output 6, .invoke, .input 6, .input 6] do
        throwError "caller signing packet changed fresh-query order"
      pure after
    | _ => throwError "caller signing packet failed to return a fresh signature with bounded resources"
  unless signed == store programmed live freshTape publicTape do throwError "fresh signing returned the wrong shared state"
  unless run (.inl (.inr (7, 3))) signed [88] ==
      some (some (.inl (.inr 3), signed), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "hashing after signing must use managed challenge 3 even when LIVE contains zero"
  let full := store (List.replicate 3 ((7, 3), 0)) (List.replicate 3 ((9, 9), 1)) (List.replicate 6 (3, 0, 0)) []
  unless run (.inl (.inr (7, 3))) full [88] ==
      some (some (.inl (.inr 0), full), [], [88], #[77], 4, 91, 9, true, true) do
    throwError "caller imposed a signing or miss reservation on a full managed hit"
  unless run (.inr 7) (store managed live saved publicTape) [6, 3] == none &&
      run (.inl (.inl 7)) (store managed live saved []) [7] == none do
    throwError "caller returned with incomplete randomness"
  unless run (.inr 7) full [] == none && run (.inl (.inl 7)) full [] == none &&
      run (.inl (.inr (10, 10))) full [] == none do throwError "caller admitted an exhausted branch"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``CallerHandler.refines, ``CallerHandler.source_original, ``CallerHandler.synchronizes, ``CallerHandler.observe_original,
      ``CallerHandler.time_bound, ``CallerHandler.code_bound, ``CallerHandler.names, ``CallerHandler.buffers, ``CallerHandler.descriptionFits,
      ``CallerHandler.resources, ``Handler.reserved_empty, ``CallerPackets.reserved_ready, ``Handler.reserved_final,
      ``CallerHandler.reserved_after, ``CallerPackets.request_bytes, ``CallerPackets.service_ready, ``matches_original] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMCaller
