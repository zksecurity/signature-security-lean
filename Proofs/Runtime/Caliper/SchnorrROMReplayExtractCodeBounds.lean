import Proofs.Runtime.Caliper.SchnorrROMReplayExtractBounds

/-! Resources of the complete interactive extractor: the executed classifier,
the stored-tag dispatch, the charged uniform draw on the fallback path and the
retained quotient. Every visited state is bounded on the execution that returns
the represented scalar. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

/-- The stored-tag selection costs at most the draw plus dispatch overhead. -/
theorem select_time : Interactive.TimeBound (Fresh.port config.handler.sampler.tape) .unit
    (choice config) (select config) 28 := by
  have bounded := Interactive.TimeBound.dispatch config.handler.sampler.tape.unit.representation
    config.handler.sampler.tape.scalar.representation (PrivateSampler.Enumerated.Direct.time_bound config.sampler)
    (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit) (keep config) 0
      (fun _ => le_rfl))
    (width_pos config.sampler.wordFits) (choiceFits config)
  rw [Interactive.dispatchTime_unit, unit_words, scalar_words] at bounded
  exact bounded

theorem select_words : ((select config).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ 193 := by
  have drawn := PrivateSampler.Enumerated.Direct.code_words config.sampler
  change ((PrivateSampler.Enumerated.Direct.code config.sampler).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ 125 at drawn
  have kept : ((Interactive.Code.compute (keep config).code).lower (Fresh.port config.handler.sampler.tape)).descriptionWords = 2 := by
    simp only [Interactive.Code.lower, WordIO.Code.descriptionWords_compute]; rfl
  unfold select draw
  rw [Interactive.dispatch_descriptionWords, unit_words, scalar_words, kept]
  omega

theorem select_buffers : ((select config).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 2 := by
  have drawn := PrivateSampler.Enumerated.Direct.buffers config.sampler
  change ((PrivateSampler.Enumerated.Direct.code config.sampler).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 2 at drawn
  refine (Interactive.dispatch_buffers _ _ _ _ _).trans (max_le le_rfl (max_le drawn ?_))
  change (Stmt.skip : Stmt w).memBound ≤ 2
  simp [Stmt.memBound]

theorem select_names : WordIO.NamesAccounted ((select config).lower (Fresh.port config.handler.sampler.tape)) 3 :=
  Interactive.dispatch_names (Fresh.port config.handler.sampler.tape)
    (PrivateSampler.Enumerated.Direct.names config.sampler).accounted
    (show WordIO.NamesAccounted ((Interactive.Code.compute (keep config).code).lower (Fresh.port config.handler.sampler.tape)) 3 from WordIO.NamesAccounted.compute (skip_names 3)) _ _

theorem select_descriptionFits : ((select config).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  Interactive.dispatch_descriptionFits (Fresh.port config.handler.sampler.tape) _ _ _ _ config.sampler.wordFits
    (PrivateSampler.Enumerated.Direct.descriptionFits config.sampler)
    (WordIO.Code.DescriptionFits.compute (keep config).description_fits)
    (by rw [unit_words]; exact Nat.two_pow_pos w) (by rw [scalar_words]; exact Nat.one_lt_two_pow (width_pos config.sampler.wordFits).ne')

section Code
variable [DecidableEq F] [DecidableEq G] [Sub F] [Div F] (arith : Arithmetic config) (budget : Arithmetic.Budget config arith)

/-- Time budget of the whole extractor in terms of the primitive budgets. -/
def timeBudget : Nat := classifyTime config (coreTime config budget.subTime budget.divideTime) + 28
/-- Stored-code budget of the whole extractor in terms of the primitive budgets. -/
def codeBudget : Nat := classifyWords config (coreWords config budget.subWords budget.divideWords) + 195
/-- Name budget: the primitive buffer names, the fixed scratch names and the draw's names. -/
def nameBudget : Nat := nameSlots config arith

theorem time : Interactive.TimeBound (Fresh.port config.handler.sampler.tape) .unit (output config)
    (code config arith) (timeBudget config arith budget) :=
  Interactive.TimeBound.seq (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (classifier config arith))
    (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
      (classifier config arith) _ (classifier_bounded config arith budget).time_le)
    (select_time config)

theorem words : ((code config arith).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    codeBudget config arith budget := by
  have classified := (classifier_bounded config arith budget).code_le
  have selected := select_words config
  change (WordIO.Code.seq (.compute (classifier config arith).code)
    ((select config).lower (Fresh.port config.handler.sampler.tape))).descriptionWords ≤ _
  rw [WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names : WordIO.NamesAccounted ((code config arith).lower (Fresh.port config.handler.sampler.tape))
    (nameBudget config arith) :=
  (WordIO.NamesAccounted.compute (classifier_names config arith)).seq
    ((select_names config).mono (by unfold nameSlots; omega))

theorem buffers : ((code config arith).lower (Fresh.port config.handler.sampler.tape)).memBound ≤
    bufferBudget config arith := by
  have classified := classifier_buffers config arith
  have selected := select_buffers config
  change max (classifier config arith).code.memBound ((select config).lower _).memBound ≤ _
  have : 2 ≤ bufferBudget config arith := by unfold bufferBudget; omega
  omega

theorem descriptionFits : ((code config arith).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  .seq config.sampler.wordFits (.compute (classifier config arith).description_fits) (select_descriptionFits config)

/-- Every execution of the extractor stays within the derived time budget,
returns a represented answer of the source, and every visited state obeys the
register, buffer and total-memory bounds. -/
theorem resources (tape : RandomTape w) (value : Result config) (before : State w)
    (holds : (output config).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code config arith).execute (Fresh.port config.handler.sampler.tape) .unit tape before)) :
    let lowered := (code config arith).lower (Fresh.port config.handler.sampler.tape)
    finished.time ≤ timeBudget config arith budget ∧ ∃ answer ∈ support (source config value),
      config.handler.sampler.tape.scalar.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape lowered before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers lowered.registerSlots) ∧ between.SupportBound (max buffers lowered.memBound) ∧
          between.WellFormed ∧
          (lowered.staticWords registers buffers : Int) + between.liveMem (max buffers lowered.memBound) ≤
            codeBudget config arith budget + 4 * (nameBudget config arith + codeBudget config arith budget) +
              registers + 3 * buffers + before.liveMem buffers + timeBudget config arith budget := by
  have stored := words config arith budget
  have named := names config arith
  exact (refines config arith).resources (time config arith budget) stored
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
    tape value before holds registers buffers initialRegisters initialBuffers finished reached

end Code
end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
