import Signatures.Runtime.Caliper.SchnorrROMReplaySecondSelectionBounds

/-! Execute the initialized first pass and select its fork point while retaining
its complete terminal output. Admission reserves both passes' tape growth. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFirst
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec ByteRoute
variable {w : Nat} {M F G A : Type} (config : Signing.Enumerated.Configuration w M F G)

instance (fuel : Nat) : DecidablePred (Pass.Replay.ready config fuel) := fun _ => by
  unfold Pass.Replay.ready
  infer_instance
def input (fuel : Nat) := (Pass.Initialization.input config).restrict (Pass.Replay.ready config fuel)
def prepared := (ReplaySecond.first config).prod (ReplaySecond.first config)
  (ReplaySecond.combinedFits config (by omega))
def output := (Selection.result config).representation.prod (ReplaySecond.first config)
  (ReplaySecond.combinedFits config (by change (1 + 1) + _ ≤ _; omega))
def duplicateParts : List (Part w) :=
  [.slice 0 (ReplaySecond.first config).encoding.words, .slice 0 (ReplaySecond.first config).encoding.words]
theorem duplicate_valid : Valid (ReplaySecond.first config).encoding.words (duplicateParts config) :=
  ⟨by omega, by omega, trivial⟩
theorem duplicate_size : words (duplicateParts config) = (prepared config).encoding.words := by
  change _ + (_ + 0) = _ + _
  omega
theorem duplicate_bytes (value : Terminal.Output config) :
    bytes ((ReplaySecond.first config).encoding.encode value) (duplicateParts config) =
      (prepared config).encoding.encode (value, value) := by
  have one := slice_block [] ((ReplaySecond.first config).encoding.encode value) []
  simp only [List.length_nil, List.nil_append, List.append_nil, Encoding.encode_length] at one
  change bytes ((ReplaySecond.first config).encoding.encode value) (duplicateParts config) =
    (ReplaySecond.first config).encoding.encode value ++ (ReplaySecond.first config).encoding.encode value
  simp only [duplicateParts, bytes, List.append_nil, one]
def duplicate : Realizer .unit (ReplaySecond.first config) (prepared config) (fun value => (value, value)) :=
  ByteRoute.realizer _ _ _ (duplicateParts config) config.sampler.wordFits
    (duplicate_valid config) (duplicate_size config) (duplicate_bytes config)

variable [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (caller : Pass.Caller config A) (ops : Handler.Operations config) (qH : Nat) (indexFits : qH + 1 < 2 ^ w)

def selectedValue (value : Terminal.Output config) : (Selection.result config).Value × Terminal.Output config :=
  (⟨PassSelection.source config qH value, PassSelection.valid config ops qH indexFits value⟩, value)
def retainedSelector := (PassSelection.realizer config ops qH indexFits).retain (by decide) (ReplaySecond.first config)
  config.sampler.wordFits (ReplayMatch.selectionNameFits config ops qH indexFits) (prepared config).fits (output config).fits
def selector : Realizer .unit (ReplaySecond.first config) (output config) (selectedValue config ops qH indexFits) :=
  (duplicate config).then (retainedSelector config ops qH indexFits)
def program (fuel : Nat) : Interactive.Code w :=
  .seq (Pass.program config caller ops fuel) (.compute (selector config ops qH indexFits).code)
def source (fuel : Nat) (value : {value : Pass.Initialization.Input config // Pass.Replay.ready config fuel value}) :=
  selectedValue config ops qH indexFits <$> Pass.source config caller ops fuel value.val

theorem pass_refines (fuel : Nat) : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit
    (input config fuel) (ReplaySecond.first config) (fun value => Pass.source config caller ops fuel value.val)
      (Pass.program config caller ops fuel) := by
  have admitted : Interactive.RefinesOn (Pass.Replay.ready config fuel) (Fresh.port config.handler.sampler.tape) .unit
      (Pass.Initialization.input config) (Pass.output config caller) (Pass.source config caller ops fuel) (Pass.program config caller ops fuel) :=
    fun tape value room => Pass.refines config caller ops fuel tape value (Pass.Replay.first_ready config fuel value room)
  unfold ReplayFirst.input
  simpa only [id_map] using (admitted.viewOutput (ReplaySecond.first config) id
    (PassSelection.pass_bytes config (caller.pending config) (caller.terminalRoom config))).restrict

theorem refines (fuel : Nat) : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit
    (input config fuel) (output config) (source config caller ops qH indexFits fuel) (program config caller ops qH indexFits fuel) := by
  unfold ReplayFirst.source ReplayFirst.program
  simpa only [bind_pure_comp] using (pass_refines config caller ops fuel).seq
    (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (selector config ops qH indexFits))

theorem next_ready (fuel : Nat) (value : {value : Pass.Initialization.Input config // Pass.Replay.ready config fuel value})
    (answer) (reached : answer ∈ support (source config caller ops qH indexFits fuel value))
    (slot : config.handler.sampler.tape.counter.Value) (replacement : config.handler.sampler.tape.scalar.Value) :
    ReplaySecond.ready config fuel ((slot, replacement), answer.2) := by
  simp only [ReplayFirst.source, support_map, Set.mem_image] at reached
  obtain ⟨first, reached, rfl⟩ := reached
  exact ReplaySecond.ready_after_first config caller ops fuel value.val value.property first reached slot replacement

theorem selector_buffers : (selector config ops qH indexFits).code.memBound ≤ max 8 (ops.slots + 3) + 1 := by
  have duplicated : (duplicate config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
  have retained := (PassSelection.realizer config ops qH indexFits).retain_buffers (by decide) (ReplaySecond.first config)
    config.sampler.wordFits (ReplayMatch.selectionNameFits config ops qH indexFits) (prepared config).fits (output config).fits
  have selected := PassSelection.buffers config ops qH indexFits
  change max (duplicate config).code.memBound (retainedSelector config ops qH indexFits).code.memBound ≤ _
  change (retainedSelector config ops qH indexFits).code.memBound ≤ _ at retained
  omega

theorem selector_names : NamesAccounted (selector config ops qH indexFits).code (max 3 ops.slots) :=
  (ByteRoute.names _ _ _ _ _ _ _ _ _).seq (Retain.names (PassSelection.names config ops qH indexFits) _ _ _)

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFirst
