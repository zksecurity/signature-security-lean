import Signatures.Runtime.Caliper.SchnorrROMReplayFirst

/-! The first-pass account includes initialization, the caller, selection and
all copies that preserve the original output for replay and extraction. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFirst
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Pass.Caller config A) (ops : Handler.Operations config)
    (qH : Nat) (indexFits : qH + 1 < 2 ^ w) (budget : Handler.Budget config ops)
    (localBudget : SchnorrROM.Caller.LocalBudget config (caller.routines config))

def selectorTime := PassSelection.timeBudget config ops qH indexFits budget +
  36 * (ReplaySecond.first config).encoding.words + 8 * (Selection.result config).representation.encoding.words
def selectorWords := PassSelection.codeBudget config ops qH indexFits budget +
  117 * (ReplaySecond.first config).encoding.words + 26 * (Selection.result config).representation.encoding.words + 54
theorem selector_time (value : Terminal.Output config) : (selector config ops qH indexFits).time value ≤ selectorTime config ops qH indexFits budget := by
  have duplicated : (duplicate config).time value ≤ 8 * (prepared config).encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ _
  have retained := (PassSelection.realizer config ops qH indexFits).retain_time_unit_le (ReplaySecond.first config)
    config.sampler.wordFits (ReplayMatch.selectionNameFits config ops qH indexFits) (prepared config).fits (output config).fits (value, value)
  have selected := PassSelection.time config ops qH indexFits budget value
  simp only at retained
  change _ ≤ _ + 8 * (ReplaySecond.first config).encoding.words + 8 * (Selection.result config).representation.encoding.words +
    12 * (ReplaySecond.first config).encoding.words at retained
  change (duplicate config).time value + (retainedSelector config ops qH indexFits).time (value, value) ≤ _
  change (retainedSelector config ops qH indexFits).time (value, value) ≤ _ at retained
  change (duplicate config).time value ≤ 8 * ((ReplaySecond.first config).encoding.words + (ReplaySecond.first config).encoding.words) at duplicated
  unfold selectorTime
  omega
theorem selector_words : descriptionWords (selector config ops qH indexFits).code ≤ selectorWords config ops qH indexFits budget := by
  have duplicated : descriptionWords (duplicate config).code ≤ 26 * (prepared config).encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
  have retained := (PassSelection.realizer config ops qH indexFits).retain_descriptionWords_le (by decide) (ReplaySecond.first config)
    config.sampler.wordFits (ReplayMatch.selectionNameFits config ops qH indexFits) (prepared config).fits (output config).fits
  have selected := PassSelection.words config ops qH indexFits budget
  change _ ≤ _ + 26 * (ReplaySecond.first config).encoding.words + 26 * (Selection.result config).representation.encoding.words +
    39 * (ReplaySecond.first config).encoding.words + 39 at retained
  change descriptionWords (retainedSelector config ops qH indexFits).code ≤ _ at retained
  change descriptionWords ((duplicate config).code ;; (retainedSelector config ops qH indexFits).code) ≤ _
  rw [descriptionWords_seq]
  change descriptionWords (duplicate config).code ≤ 26 * ((ReplaySecond.first config).encoding.words + (ReplaySecond.first config).encoding.words) + 14 at duplicated
  unfold selectorWords
  omega

def timeBudget (fuel : Nat) := Pass.timeBudget config caller ops budget localBudget fuel + selectorTime config ops qH indexFits budget
def codeBudget (fuel : Nat) := Pass.codeBudget config caller ops budget localBudget fuel + selectorWords config ops qH indexFits budget + 2
omit [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G] in
def nameBudget (slots : Nat) := max (Pass.nameBudget config slots) (max 3 ops.slots)

theorem time (fuel : Nat) : Interactive.TimeBound (Fresh.port config.handler.sampler.tape) .unit
    (input config fuel) (program config caller ops qH indexFits fuel) (timeBudget config caller ops qH indexFits budget localBudget fuel) := by
  have admitted : Interactive.TimeBoundOn (Pass.Replay.ready config fuel) (Fresh.port config.handler.sampler.tape) .unit
      (Pass.Initialization.input config) (Pass.program config caller ops fuel) (Pass.timeBudget config caller ops budget localBudget fuel) :=
    fun tape value room => Pass.time config caller ops budget localBudget fuel tape value (Pass.Replay.first_ready config fuel value room)
  have selecting := Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
    (selector config ops qH indexFits) _ (selector_time config ops qH indexFits budget)
  exact Interactive.TimeBound.seq (pass_refines config caller ops fuel) admitted.restrict selecting

theorem words (fuel : Nat) : ((program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    codeBudget config caller ops qH indexFits budget localBudget fuel := by
  have first := Pass.words config caller ops budget localBudget fuel
  have selected := selector_words config ops qH indexFits budget
  change (WordIO.Code.seq ((Pass.program config caller ops fuel).lower _) (.compute (selector config ops qH indexFits).code)).descriptionWords ≤ _
  rw [WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) : WordIO.NamesAccounted ((program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)) (nameBudget config ops slots) :=
  ((Pass.names config caller ops slots handlerRoom localNames initialNames fuel).mono (Nat.le_max_left _ _)).seq
    ((WordIO.NamesAccounted.compute (selector_names config ops qH indexFits)).mono (Nat.le_max_right _ _))

theorem buffers (fuel : Nat) : ((program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).memBound ≤
    Pass.bufferBudget config caller ops + 1 := by
  have first := Pass.buffers config caller ops fuel
  have selected := selector_buffers config ops qH indexFits
  change max ((Pass.program config caller ops fuel).lower _).memBound (selector config ops qH indexFits).code.memBound ≤ _
  unfold Pass.bufferBudget at *
  omega

theorem descriptionFits (fuel : Nat) : ((program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  .seq config.sampler.wordFits (Pass.descriptionFits config caller ops fuel) (.compute (selector config ops qH indexFits).description_fits)

theorem resources (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) (tape : RandomTape w) (value : {value : Pass.Initialization.Input config // Pass.Replay.ready config fuel value})
    (before : State w) (holds : (input config fuel).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program config caller ops qH indexFits fuel).execute (Fresh.port config.handler.sampler.tape) .unit tape before)) :
    let code := (program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)
    let stored := codeBudget config caller ops qH indexFits budget localBudget fuel
    let elapsed := timeBudget config caller ops qH indexFits budget localBudget fuel
    finished.time ≤ elapsed ∧ ∃ answer ∈ support (source config caller ops qH indexFits fuel value),
      (output config).Holds answer finished.state ∧
      (∀ slot replacement, ReplaySecond.ready config fuel ((slot, replacement), answer.2)) ∧
      ∃ execution : WordIO.Exec .unit tape code before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers code.registerSlots) ∧ between.SupportBound (max buffers code.memBound) ∧ between.WellFormed ∧
          (code.staticWords registers buffers : Int) + between.liveMem (max buffers code.memBound) ≤
            stored + 4 * (nameBudget config ops slots + stored) + registers + 3 * buffers + before.liveMem buffers + elapsed := by
  have stored := words config caller ops qH indexFits budget localBudget fuel
  have named := names config caller ops qH indexFits slots handlerRoom localNames initialNames fuel
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    (refines config caller ops qH indexFits fuel).resources (time config caller ops qH indexFits budget localBudget fuel) stored
      ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
      tape value before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, represented, next_ready config caller ops qH indexFits fuel value answer supported, execution, memory⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFirst
