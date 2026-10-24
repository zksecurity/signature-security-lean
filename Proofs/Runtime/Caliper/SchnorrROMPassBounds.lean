import Proofs.Runtime.Caliper.SchnorrROMPass

/-! Complete pass resources include initialization, the generated caller and
final hashing. The output and all visited memory refer to the same execution. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Pass
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Caller config A) (ops : Handler.Operations config)
    (budget : Handler.Budget config ops) (localBudget : SchnorrROM.Caller.LocalBudget config (caller.routines config))

def timeBudget (fuel : Nat) := 8 * (Initialization.output config).encoding.words + finishTime config caller ops budget localBudget fuel
def codeBudget (fuel : Nat) := 26 * (Initialization.output config).encoding.words + finishWords config caller ops budget localBudget fuel + 16

theorem time (fuel : Nat) : Interactive.TimeBoundOn (Initialization.admitted config fuel) (Fresh.port config.handler.sampler.tape) .unit
    (Initialization.input config) (program config caller ops fuel) (timeBudget config caller ops budget localBudget fuel) :=
  Interactive.TimeBoundOn.seq
    ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (Initialization.code config)).on (Initialization.admitted config fuel))
    ((Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
      (Initialization.code config) _ (Initialization.time config)).on (Initialization.admitted config fuel))
    (finish_time config caller ops budget localBudget fuel) (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact Initialization.reserved config fuel value valid)

theorem words (fuel : Nat) : ((program config caller ops fuel).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    codeBudget config caller ops budget localBudget fuel := by
  have initialized := Initialization.words config
  have completed := finish_words config caller ops budget localBudget fuel
  change (WordIO.Code.seq (.compute (Initialization.code config).code)
    ((finishCode config caller ops fuel).lower (Fresh.port config.handler.sampler.tape))).descriptionWords ≤ _
  rw [WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) : WordIO.NamesAccounted ((program config caller ops fuel).lower (Fresh.port config.handler.sampler.tape))
      (nameBudget config slots) :=
  (WordIO.NamesAccounted.compute (Initialization.names config _)).seq
    (finish_names config caller ops slots handlerRoom localNames initialNames fuel)

theorem descriptionFits (fuel : Nat) : ((program config caller ops fuel).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  .seq config.sampler.wordFits (.compute (Initialization.code config).description_fits) (finish_descriptionFits config caller ops fuel)

theorem resources (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) (tape : RandomTape w) (value : Initialization.Input config) (room : Initialization.admitted config fuel value)
    (before : State w) (holds : (Initialization.input config).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program config caller ops fuel).execute (Fresh.port config.handler.sampler.tape) .unit tape before)) :
    let code := (program config caller ops fuel).lower (Fresh.port config.handler.sampler.tape)
    let stored := codeBudget config caller ops budget localBudget fuel
    let elapsed := timeBudget config caller ops budget localBudget fuel
    finished.time ≤ elapsed ∧ ∃ answer ∈ support (source config caller ops fuel value),
      (output config caller).Holds answer finished.state ∧ answer.2.val.1.1 = value.2.val ∧
      ∃ execution : WordIO.Exec .unit tape code before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers code.registerSlots) ∧ between.SupportBound (max buffers code.memBound) ∧ between.WellFormed ∧
          (code.staticWords registers buffers : Int) + between.liveMem (max buffers code.memBound) ≤
            stored + 4 * (nameBudget config slots + stored) + registers + 3 * buffers + before.liveMem buffers + elapsed := by
  have stored := words config caller ops budget localBudget fuel
  have named := names config caller ops slots handlerRoom localNames initialNames fuel
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    (refines config caller ops fuel).resources (time config caller ops budget localBudget fuel) stored
      ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
      tape value room before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, represented, preserves_config config caller ops fuel value room answer supported, execution, memory⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.Pass
