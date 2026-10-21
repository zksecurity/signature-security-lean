import Signatures.Runtime.Caliper.SchnorrROMReplayChallengeGuardBounds

/-! Draw a fresh challenge and execute its original saved-tape rejection test.
This phase retains the complete request needed to run the second pass. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayChallenge.Checked
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [DecidableEq F] (config : Signing.Enumerated.Configuration w M F G)

def program : Interactive.Code w := .seq (ReplayChallenge.program config) (.compute (Guard.realizer config).code)
def source (value : Input config) : ProbComp (config.handler.sampler.tape.boolean.Value × ReplaySecond.Request config) := (fun request : ReplaySecond.Request config => Guard.source config request) <$> ReplayChallenge.source config value

theorem refines : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit
    (input config) (Guard.output config) (source config) (program config) := by
  have joined := (ReplayChallenge.refines config).seq
    (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (Guard.realizer config))
  have sourceEq (value : Input config) :
      (do let request ← ReplayChallenge.source config value; pure (Guard.source config request)) = source config value := by
    unfold ReplayChallenge.Checked.source
    exact bind_pure_comp (fun request : ReplaySecond.Request config => Guard.source config request) (ReplayChallenge.source config value)
  intro tape value before holds
  change Synchronizes _ (source config value) _
  rw [← sourceEq value]
  exact joined tape value before holds

theorem retains_first (value : Input config) (answer) (reached : answer ∈ support (source config value)) :
    answer.2.2 = value.2 ∧ answer.2.1.1 = value.1 := by
  change answer ∈ support ((fun request : ReplaySecond.Request config => Guard.source config request) <$> ReplayChallenge.source config value) at reached
  erw [support_map] at reached
  simp only [Set.mem_image] at reached
  obtain ⟨request, reached, rfl⟩ := reached
  exact ReplayChallenge.retains_first config value request reached

theorem source_original [Zero F] (value : Input config) :
    (fun answer : config.handler.sampler.tape.boolean.Value × ReplaySecond.Request config =>
      (answer.1.val, answer.2)) <$> source config value =
      (fun request : ReplaySecond.Request config =>
        (decide ((Schnorr.RawTape.values (.inr ()) request.2.2.val.2.1)[request.1.1.val]? = some request.1.2.val), request)) <$>
          ReplayChallenge.source config value := by
  unfold ReplayChallenge.Checked.source
  erw [Functor.map_map]
  apply congrArg (fun observe : ReplaySecond.Request config → Bool × ReplaySecond.Request config =>
    observe <$> ReplayChallenge.source config value)
  funext request
  apply Prod.ext
  · exact Guard.source_original config request
  · rfl

def timeBudget := ReplayChallenge.timeBudget config + Guard.timeBudget config
def codeBudget := ReplayChallenge.codeBudget config + Guard.codeBudget config + 2

theorem time : Interactive.TimeBound (Fresh.port config.handler.sampler.tape) .unit (input config) (program config) (timeBudget config) :=
  Interactive.TimeBound.seq (ReplayChallenge.refines config) (ReplayChallenge.time config)
    (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit) (Guard.realizer config) _ (Guard.time config))
theorem words : ((program config).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ codeBudget config := by
  have sampled := ReplayChallenge.words config
  have tested := Guard.words config
  change (WordIO.Code.seq ((ReplayChallenge.program config).lower _) (.compute (Guard.realizer config).code)).descriptionWords ≤ _
  rw [WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names : WordIO.NamesAccounted ((program config).lower (Fresh.port config.handler.sampler.tape)) 3 :=
  (ReplayChallenge.names config).seq (WordIO.NamesAccounted.compute (Guard.names config 3))
theorem buffers : ((program config).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 9 :=
  max_le ((ReplayChallenge.buffers config).trans (by decide)) (Guard.buffers config)
theorem descriptionFits : ((program config).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  .seq config.sampler.wordFits (ReplayChallenge.descriptionFits config) (.compute (Guard.realizer config).description_fits)

theorem resources (tape : RandomTape w) (value : Input config) (before : State w) (holds : (input config).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program config).execute (Fresh.port config.handler.sampler.tape) .unit tape before)) :
    let code := (program config).lower (Fresh.port config.handler.sampler.tape)
    finished.time ≤ timeBudget config ∧ ∃ answer ∈ support (source config value),
      (Guard.output config).Holds answer finished.state ∧ answer.2.2 = value.2 ∧ answer.2.1.1 = value.1 ∧
      ∃ execution : WordIO.Exec .unit tape code before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers code.registerSlots) ∧ between.SupportBound (max buffers code.memBound) ∧ between.WellFormed ∧
          (code.staticWords registers buffers : Int) + between.liveMem (max buffers code.memBound) ≤
            codeBudget config + 4 * (3 + codeBudget config) + registers + 3 * buffers + before.liveMem buffers + timeBudget config := by
  have stored := words config
  have named := names config
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    (refines config).resources (time config) stored
      ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
      tape value before holds registers buffers initialRegisters initialBuffers finished reached
  have retained := retains_first config value answer supported
  exact ⟨elapsed, answer, supported, represented, retained.1, retained.2, execution, memory⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayChallenge.Checked
