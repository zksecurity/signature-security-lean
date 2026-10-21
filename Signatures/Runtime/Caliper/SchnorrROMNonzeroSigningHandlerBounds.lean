import Signatures.Runtime.Caliper.SchnorrROMNonzeroSigningSource

/-! Resource bounds of the executed nonzero signing branch, derived from the
local implementation: both replayed field draws and the replayed nonzero draw
(with their retained contexts), every executed route, the guarded suffix and the
managed-cache programmer. Time, stored code words, accounted buffer names,
buffers, description fitting and all visited memory are covered. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.NonzeroSigning
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

section Bounds
variable [Zero F] [SMul F G] [Sub G] [Add F] [DecidableEq M] [DecidableEq G]
    (ops : Handler.Operations config) (arith : Arithmetic config) (positive : 0 < config.sampler.bound)
    {scaleTime scaleWords subTime subWords addTime addWords : Nat}
    (scaleBound : ops.scale.BoundedBy scaleTime scaleWords) (subBound : ops.sub.BoundedBy subTime subWords)
    (addBound : arith.add.BoundedBy addTime addWords)

/-! ### The final routed and retained suffix -/

def finishTime (scaleTime subTime addTime : Nat) := timeBudget config scaleTime subTime addTime +
  8 * (work config).encoding.words + 8 * (nzInput config).representation.encoding.words +
  8 * config.handler.core.output.representation.encoding.words + 12 * config.handler.saved.representation.encoding.words
def finishWords (scaleWords subWords addWords : Nat) := codeBudget config scaleWords subWords addWords +
  26 * (work config).encoding.words + 26 * (nzInput config).representation.encoding.words +
  26 * config.handler.core.output.representation.encoding.words + 39 * config.handler.saved.representation.encoding.words + 54

include scaleBound subBound addBound in
theorem finish_time (value : (Reply.scalarOutput config.handler.sampler.tape).Value ×
    (config.handler.core.arithmetic.scalars.Value × config.handler.context.Value)) :
    (finish config ops arith).time value ≤ finishTime config scaleTime subTime addTime := by
  have computed := (bounded config ops arith scaleBound subBound addBound).time_le (workValue config value).1
  have routed : (workRoute config).time value ≤ 8 * (work config).encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ value
  have copied := (implementation config ops arith).program.retain_time_unit_le config.handler.saved.representation
    config.sampler.wordFits (coreNameFits config ops arith) (work config).fits config.handler.finished.fits (workValue config value)
  change (retainedCore config ops arith).time (workValue config value) ≤ _ at copied
  change (workRoute config).time value + (retainedCore config ops arith).time (workValue config value) ≤ _
  unfold finishTime
  omega

include scaleBound subBound addBound in
theorem finish_words : descriptionWords (finish config ops arith).code ≤ finishWords config scaleWords subWords addWords := by
  have computed := (bounded config ops arith scaleBound subBound addBound).code_le
  have routed : descriptionWords (workRoute config).code ≤ 26 * (work config).encoding.words + 14 :=
    ByteRoute.codeWords _ _ _ _ _ _ _ _
  have copied := (implementation config ops arith).program.retain_descriptionWords_le (by decide)
    config.handler.saved.representation config.sampler.wordFits (coreNameFits config ops arith) (work config).fits
    config.handler.finished.fits
  change descriptionWords (retainedCore config ops arith).code ≤ _ at copied
  change descriptionWords ((workRoute config).code ;; (retainedCore config ops arith).code) ≤ _
  rw [descriptionWords_seq]
  unfold finishWords
  omega

theorem finish_buffers : (finish config ops arith).code.memBound ≤ max 10 (slots config ops arith + 4) := by
  have computed := buffers config ops arith
  have copied := (implementation config ops arith).program.retain_buffers (by decide) config.handler.saved.representation
    config.sampler.wordFits (coreNameFits config ops arith) (work config).fits config.handler.finished.fits
  have routed : (workRoute config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
  change (retainedCore config ops arith).code.memBound ≤ _ at copied
  change max (workRoute config).code.memBound (retainedCore config ops arith).code.memBound ≤ _
  omega

theorem finish_names (names : Nat) (scaleNames : NamesAccounted ops.scale.program.code names)
    (subNames : NamesAccounted ops.sub.program.code names) (addNames : NamesAccounted arith.add.program.code names) :
    NamesAccounted (finish config ops arith).code (max 5 names) :=
  (ByteRoute.names _ _ _ _ _ _ _ _ _).seq (Retain.names
    (NonzeroSigning.names config ops arith names scaleNames subNames addNames) _ _ _)

/-! ### The whole branch -/

/-- Time budget: two enumerated field draws, one nonzero draw, every route and
retained copy, and the deterministic suffix. -/
def handlerTime (scaleTime subTime addTime : Nat) :=
  PrivateSampler.Pair.timeBudget config.handler.sampler trivial 38 16 1 +
  8 * config.handler.prepared.encoding.words + 8 * (Read.tapes config.handler.sampler.tape).representation.encoding.words +
  8 * (PrivateSampler.Pair.output config.handler.sampler).representation.encoding.words +
  12 * config.handler.context.representation.encoding.words +
  8 * (middle config).encoding.words +
  PrivateSampler.Service.timeBudget config.handler.sampler trivial 186 16 1 +
  8 * (Read.tapes config.handler.sampler.tape).representation.encoding.words +
  8 * (Reply.scalarOutput config.handler.sampler.tape).representation.encoding.words + 12 * (pairCtx config).encoding.words +
  finishTime config scaleTime subTime addTime

/-- Stored-code budget of the branch. -/
def handlerWords (scaleWords subWords addWords : Nat) :=
  PrivateSampler.Pair.codeBudget config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler) trivial 1 +
  26 * config.handler.prepared.encoding.words + 26 * (Read.tapes config.handler.sampler.tape).representation.encoding.words +
  26 * (PrivateSampler.Pair.output config.handler.sampler).representation.encoding.words +
  39 * config.handler.context.representation.encoding.words +
  26 * (middle config).encoding.words +
  PrivateSampler.Service.codeBudget config.handler.sampler (nonzeroCaller config positive) trivial 1 +
  26 * (Read.tapes config.handler.sampler.tape).representation.encoding.words +
  26 * (Reply.scalarOutput config.handler.sampler.tape).representation.encoding.words + 39 * (pairCtx config).encoding.words +
  finishWords config scaleWords subWords addWords + 200

/-- Accounted names of the branch. -/
def handlerNames (primitiveNames : Nat) := max (PrivateSampler.nameBudget config.handler.sampler trivial 3) (max 5 primitiveNames)

omit [SMul F G] [Sub G] [Add F] [DecidableEq M] [DecidableEq G] in
theorem pair_refines : Interactive.RefinesOn
    (fun value : PrivateSampler.Store config.handler.sampler × config.handler.context.Value =>
      PrivateHandler.Reserved config.handler.sampler.tape 3 value.1)
    (Fresh.port config.handler.sampler.tape) .unit config.handler.prepared config.handler.sampled
    (fun value => (fun answer => (answer, value.2)) <$> PrivateSampler.Pair.source config.handler.sampler
      (PrivateSampler.Enumerated.caller config.sampler) trivial 1 value.1)
    (Signing.Handler.retained config.handler trivial (PrivateSampler.Enumerated.caller config.sampler) 1) :=
  fun tape value valid before holds =>
    Signing.Handler.retained_refines config.handler trivial (PrivateSampler.Enumerated.caller config.sampler) 1 tape value
      (by unfold PrivateHandler.Reserved at valid
          change value.1.val.1.length + (1 + 1) ≤ config.handler.sampler.tape.capacity
          omega) before holds

include scaleBound subBound addBound in
theorem time_bound : Interactive.TimeBoundOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    config.handler.input.representation (code config ops arith positive) (handlerTime config scaleTime subTime addTime) := by
  have nonceRefines := (PrivateSampler.Service.refines config.handler.sampler (nonzeroCaller config positive) trivial 1).retain
    (by decide) (pairCtx config) config.sampler.wordFits (middle config).fits (drawn config).fits
  have nonceHeld := (Interactive.TimeBoundOn.retain
    (PrivateSampler.Service.refines config.handler.sampler (nonzeroCaller config positive) trivial 1)
    (PrivateSampler.Service.time_bound config.handler.sampler (nonzeroCaller config positive) trivial 1 186 16
      (PrivateSampler.Enumerated.Nonzero.continuation_time config.sampler positive)
      (PrivateSampler.Enumerated.Nonzero.initial_time config.sampler))
    (by decide) (pairCtx config) config.sampler.wordFits (middle config).fits).mono
      (Interactive.retain_time_unit_le _ _ _ _ _)
  have finished := (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
    (finish config ops arith) (finishTime config scaleTime subTime addTime)
    (finish_time config ops arith scaleBound subBound addBound)).on (fun _ => True)
  have nonceTail := Interactive.TimeBoundOn.seq nonceRefines nonceHeld finished (by intros; trivial)
  have movedTime := (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
    (midRoute config) (8 * (middle config).encoding.words) (fun value => ByteRoute.time _ _ _ _ _ _ _ _ value)).on
      (fun value => PrivateSampler.Service.ready config.handler.sampler 1 (midValue config value).1)
  have finishedRefines := nonceRefines.seq
    ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (finish config ops arith)).on (fun _ => True))
    (by intros; trivial)
  have movedTail := Interactive.TimeBoundOn.seq
    ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (midRoute config)).on
      (fun value => PrivateSampler.Service.ready config.handler.sampler 1 (midValue config value).1))
    movedTime nonceTail (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact valid)
  have pairTime := (Interactive.TimeBoundOn.retain
    (PrivateSampler.Pair.refines config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler) trivial 1)
    (PrivateSampler.Pair.time_bound config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler) trivial 1 38 16
      (PrivateSampler.Enumerated.continuation_time config.sampler) (PrivateSampler.Enumerated.initial_time config.sampler))
    (by decide) config.handler.context.representation config.sampler.wordFits config.handler.prepared.fits).mono
      (Interactive.retain_time_unit_le _ _ _ _ _)
  have pairHeld : Interactive.TimeBoundOn
      (fun value : PrivateSampler.Store config.handler.sampler × config.handler.context.Value =>
        PrivateHandler.Reserved config.handler.sampler.tape 3 value.1)
      (Fresh.port config.handler.sampler.tape) .unit config.handler.prepared
      (Signing.Handler.retained config.handler trivial (PrivateSampler.Enumerated.caller config.sampler) 1) _ :=
    fun tape value valid => pairTime tape value
      (by unfold PrivateHandler.Reserved at valid
          change value.1.val.1.length + (1 + 1) ≤ config.handler.sampler.tape.capacity
          omega)
  have pairTail := Interactive.TimeBoundOn.seq (pair_refines config) pairHeld movedTail (by
    intro value valid answer reached
    simp only [support_map, Set.mem_image] at reached
    obtain ⟨sampled, supported, rfl⟩ := reached
    exact PrivateSampler.Pair.reserved_after config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler)
      trivial 1 1 value.1 valid sampled supported)
  have preparedTime := (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
    (Signing.Handler.prepare config.handler) (8 * config.handler.prepared.encoding.words)
    (Signing.Handler.prepare_time config.handler)).on (ready config)
  have combined := Interactive.TimeBoundOn.seq
    ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (Signing.Handler.prepare config.handler)).on
      (ready config)) preparedTime pairTail (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact valid)
  exact combined.mono (by unfold handlerTime; omega)

include scaleBound subBound addBound in
theorem code_bound : ((code config ops arith positive).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    handlerWords config positive scaleWords subWords addWords := by
  have sampled := PrivateSampler.Pair.code_bound config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler) trivial 1
  have drawnWords := PrivateSampler.Service.code_bound config.handler.sampler (nonzeroCaller config positive) trivial 1
  have prepared := Signing.Handler.prepare_words config.handler
  have moved : descriptionWords (midRoute config).code ≤ 26 * (middle config).encoding.words + 14 :=
    ByteRoute.codeWords _ _ _ _ _ _ _ _
  have finished := finish_words config ops arith scaleBound subBound addBound
  have pairHeld := Interactive.retain_descriptionWords_le (Fresh.port config.handler.sampler.tape)
    (PrivateSampler.Pair.code config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler) trivial 1)
    (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape)
      (PrivateSampler.Pair.code config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler) trivial 1))
    (Read.tapes config.handler.sampler.tape).representation.encoding.words
    (PrivateSampler.Pair.output config.handler.sampler).representation.encoding.words
    config.handler.context.representation.encoding.words
  have nonceHeld := Interactive.retain_descriptionWords_le (Fresh.port config.handler.sampler.tape)
    (PrivateSampler.Service.code config.handler.sampler (nonzeroCaller config positive) trivial 1)
    (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape)
      (PrivateSampler.Service.code config.handler.sampler (nonzeroCaller config positive) trivial 1))
    (Read.tapes config.handler.sampler.tape).representation.encoding.words
    (Reply.scalarOutput config.handler.sampler.tape).representation.encoding.words (pairCtx config).encoding.words
  change ((Signing.Handler.retained config.handler trivial (PrivateSampler.Enumerated.caller config.sampler) 1).lower
    (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ _ at pairHeld
  change ((retainedNonzero config positive).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ _ at nonceHeld
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold handlerWords
  omega

theorem handler_names (primitiveNames : Nat) (scaleNames : NamesAccounted ops.scale.program.code primitiveNames)
    (subNames : NamesAccounted ops.sub.program.code primitiveNames)
    (addNames : NamesAccounted arith.add.program.code primitiveNames) :
    WordIO.NamesAccounted ((code config ops arith positive).lower (Fresh.port config.handler.sampler.tape))
      (handlerNames config primitiveNames) := by
  have pairHeld := Interactive.retain_names (Fresh.port config.handler.sampler.tape)
    (PrivateSampler.Pair.names config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler) trivial 1 3
      (PrivateSampler.Enumerated.continuation_names config.sampler).accounted
      (PrivateSampler.Enumerated.initial_names config.sampler).accounted)
    (Read.tapes config.handler.sampler.tape).representation.encoding.words
    (PrivateSampler.Pair.output config.handler.sampler).representation.encoding.words
    config.handler.context.representation.encoding.words
  have nonceHeld := Interactive.retain_names (Fresh.port config.handler.sampler.tape)
    (PrivateSampler.Service.names config.handler.sampler (nonzeroCaller config positive) trivial 1 3
      (PrivateSampler.Enumerated.Nonzero.continuation_names config.sampler positive)
      (PrivateSampler.Enumerated.Nonzero.initial_names config.sampler))
    (Read.tapes config.handler.sampler.tape).representation.encoding.words
    (Reply.scalarOutput config.handler.sampler.tape).representation.encoding.words (pairCtx config).encoding.words
  exact (WordIO.NamesAccounted.compute (Signing.Handler.prepare_names config.handler _)).seq
    ((pairHeld.mono (Nat.le_max_left _ _)).seq
      ((WordIO.NamesAccounted.compute (ByteRoute.names _ _ _ _ _ _ _ _ _)).seq
        ((nonceHeld.mono (Nat.le_max_left _ _)).seq (WordIO.NamesAccounted.compute
          ((finish_names config ops arith primitiveNames scaleNames subNames addNames).mono (Nat.le_max_right _ _))))))

theorem handler_buffers : ((code config ops arith positive).lower (Fresh.port config.handler.sampler.tape)).memBound ≤
    max 11 (slots config ops arith + 4) := by
  have prepared := Signing.Handler.prepare_buffers config.handler
  have sampled := PrivateSampler.Pair.buffers config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler) trivial 1
  have pairHeld := Interactive.retain_buffers (Fresh.port config.handler.sampler.tape)
    (PrivateSampler.Pair.code config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler) trivial 1)
    (Read.tapes config.handler.sampler.tape).representation.encoding.words
    (PrivateSampler.Pair.output config.handler.sampler).representation.encoding.words
    config.handler.context.representation.encoding.words
  have moved : (midRoute config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
  have drawnBuffers := PrivateSampler.Service.buffers config.handler.sampler (nonzeroCaller config positive) trivial 1
  have nonceHeld := Interactive.retain_buffers (Fresh.port config.handler.sampler.tape)
    (PrivateSampler.Service.code config.handler.sampler (nonzeroCaller config positive) trivial 1)
    (Read.tapes config.handler.sampler.tape).representation.encoding.words
    (Reply.scalarOutput config.handler.sampler.tape).representation.encoding.words (pairCtx config).encoding.words
  have finished := finish_buffers config ops arith
  have enumeratedInitial : (PrivateSampler.Enumerated.caller config.sampler).initialCode.code.memBound ≤ 2 :=
    PrivateSampler.Enumerated.initial_buffers config.sampler
  have enumeratedLocal : (PrivateSampler.Enumerated.caller config.sampler).continuation.code.memBound ≤ 2 :=
    PrivateSampler.Enumerated.continuation_buffers config.sampler
  have nonzeroInitial : (nonzeroCaller config positive).initialCode.code.memBound ≤ 2 :=
    PrivateSampler.Enumerated.Nonzero.initial_buffers config.sampler
  have nonzeroLocal : (nonzeroCaller config positive).continuation.code.memBound ≤ 3 :=
    PrivateSampler.Enumerated.Nonzero.continuation_buffers config.sampler positive
  change ((Signing.Handler.retained config.handler trivial (PrivateSampler.Enumerated.caller config.sampler) 1).lower
    (Fresh.port config.handler.sampler.tape)).memBound ≤ _ at pairHeld
  change ((retainedNonzero config positive).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ _ at nonceHeld
  change max (Signing.Handler.prepare config.handler).code.memBound
    (max ((Signing.Handler.retained config.handler trivial (PrivateSampler.Enumerated.caller config.sampler) 1).lower
      (Fresh.port config.handler.sampler.tape)).memBound
      (max (midRoute config).code.memBound
        (max ((retainedNonzero config positive).lower (Fresh.port config.handler.sampler.tape)).memBound
          (finish config ops arith).code.memBound))) ≤ _
  unfold PrivateSampler.Service.bufferBudget at *
  omega

theorem descriptionFits :
    ((code config ops arith positive).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits := by
  have pairFits := PrivateSampler.Pair.descriptionFits config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler)
    trivial 1 (by have := PrivateSampler.Enumerated.continuation_headroom config.sampler; omega)
    (by have := PrivateSampler.Enumerated.initial_headroom config.sampler; omega)
  have pairSaved : Interactive.savedBuffer (Fresh.port config.handler.sampler.tape)
      (PrivateSampler.Pair.code config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler) trivial 1) < 2 ^ w := by
    have bound := PrivateSampler.Pair.buffers config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler) trivial 1
    have := config.sampler.wordFits
    have : (PrivateSampler.Enumerated.caller config.sampler).initialCode.code.memBound ≤ 2 :=
      PrivateSampler.Enumerated.initial_buffers config.sampler
    have : (PrivateSampler.Enumerated.caller config.sampler).continuation.code.memBound ≤ 2 :=
      PrivateSampler.Enumerated.continuation_buffers config.sampler
    unfold Interactive.savedBuffer
    unfold PrivateSampler.Service.bufferBudget at bound
    omega
  have pairHeld := Interactive.retain_descriptionFits (Fresh.port config.handler.sampler.tape)
    (PrivateSampler.Pair.code config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler) trivial 1) _ _ _ _
    config.sampler.wordFits pairFits pairSaved
    (Read.tapes config.handler.sampler.tape).representation.fits config.handler.context.representation.fits
    config.handler.sampled.fits
  have nonceFits := PrivateSampler.Service.descriptionFits config.handler.sampler (nonzeroCaller config positive) trivial 1
  have nonceSaved := PrivateSampler.Service.savedBuffer_fits config.handler.sampler (nonzeroCaller config positive) trivial 1
    (by have := PrivateSampler.Enumerated.Nonzero.continuation_headroom config.sampler positive; exact Nat.lt_of_succ_lt this)
    (by have := PrivateSampler.Enumerated.Nonzero.initial_headroom config.sampler; exact Nat.lt_of_succ_lt this)
  have nonceHeld := Interactive.retain_descriptionFits (Fresh.port config.handler.sampler.tape)
    (PrivateSampler.Service.code config.handler.sampler (nonzeroCaller config positive) trivial 1) _ _ _ _
    config.sampler.wordFits nonceFits nonceSaved
    (Read.tapes config.handler.sampler.tape).representation.fits (pairCtx config).fits (drawn config).fits
  exact .seq config.sampler.wordFits (.compute (Signing.Handler.prepare config.handler).description_fits)
    (.seq config.sampler.wordFits pairHeld
      (.seq config.sampler.wordFits (.compute (midRoute config).description_fits)
        (.seq config.sampler.wordFits nonceHeld (.compute (finish config ops arith).description_fits))))

include scaleBound subBound addBound in
/-- The signing output, elapsed time, stored program and all visited memory
refer to one supported execution of the branch. -/
theorem handler_resources (primitiveNames : Nat) (scaleNamed : NamesAccounted ops.scale.program.code primitiveNames)
    (subNamed : NamesAccounted ops.sub.program.code primitiveNames)
    (addNamed : NamesAccounted arith.add.program.code primitiveNames)
    (tape : RandomTape w) (input : config.handler.input.Value) (valid : ready config input)
    (before : State w) (holds : config.handler.input.representation.Holds input before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code config ops arith positive).execute
      (Fresh.port config.handler.sampler.tape) .unit tape before)) :
    finished.time ≤ handlerTime config scaleTime subTime addTime ∧
    ∃ answer ∈ support (source config ops arith positive input),
      config.handler.output.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape
          ((code config ops arith positive).lower (Fresh.port config.handler.sampler.tape)) before
          finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers
            ((code config ops arith positive).lower (Fresh.port config.handler.sampler.tape)).registerSlots) ∧
          between.SupportBound (max buffers
            ((code config ops arith positive).lower (Fresh.port config.handler.sampler.tape)).memBound) ∧
          between.WellFormed ∧
          (((code config ops arith positive).lower (Fresh.port config.handler.sampler.tape)).staticWords registers buffers : Int) +
            between.liveMem (max buffers
              ((code config ops arith positive).lower (Fresh.port config.handler.sampler.tape)).memBound) ≤
              5 * handlerWords config positive scaleWords subWords addWords + 4 * handlerNames config primitiveNames +
                registers + 3 * buffers + before.liveMem buffers + handlerTime config scaleTime subTime addTime := by
  have words := code_bound config ops arith positive scaleBound subBound addBound
  have named := handler_names config ops arith positive primitiveNames scaleNamed subNamed addNamed
  have reserved : WordIO.NamesBound ((code config ops arith positive).lower (Fresh.port config.handler.sampler.tape))
      (handlerNames config primitiveNames + handlerWords config positive scaleWords subWords addWords) :=
    ⟨named.registers.trans (Nat.add_le_add_left words _), named.buffers.trans (Nat.add_le_add_left words _)⟩
  have checked := (refines config ops arith positive).resources
    (time_bound config ops arith positive scaleBound subBound addBound)
    words reserved tape input valid before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨elapsed, answer, supported, output, execution, visitedBound⟩ := checked
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := visitedBound between visited
  exact ⟨registerBound, bufferBound, wellFormed, by push_cast at memory; omega⟩

end Bounds
end Signatures.Runtime.CaliperBackend.SchnorrROM.NonzeroSigning
