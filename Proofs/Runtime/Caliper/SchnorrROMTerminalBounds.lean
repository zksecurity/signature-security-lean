import Proofs.Runtime.Caliper.SchnorrROMTerminal

/-! Returning and fuel cutoff have the same explicit output layout. All dispatch,
padding and store copies are charged, including code for the unused branch. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Terminal
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G P : Type} (config : Signing.Enumerated.Configuration w M F G)
    (pending : Representation w P) (room : 8 * width config pending < 2 ^ w)

theorem widths : (input config pending room).encoding.words ≤ width config pending ∧
    (ForgeryHash.input config).encoding.words ≤ width config pending ∧
    (cutoffInput config pending room).encoding.words ≤ width config pending ∧
    (output config pending room).encoding.words ≤ 2 * width config pending := by
  change (1 + max _ _ + _ ≤ _) ∧ (_ + _ ≤ _) ∧ (_ + _ ≤ _) ∧
    (1 + max 0 (_ + 1) + _ ≤ _)
  unfold width
  omega

theorem distribute_time (value) : (distribute config pending room).time value ≤ 24 * width config pending + 2 :=
  (SumContext.time _ _ _ _ _ value).trans (by
    change 24 * (input config pending room).encoding.words + 2 ≤ _
    have := (widths config pending room).1
    omega)
theorem successTag_time (value) : (successTag config pending room).time value ≤ 72 * width config pending :=
  (SumContext.mergeRight_time _ _ _ _ _ value).trans (by
    have bound := (widths config pending room).2.2.2
    change 36 * (output config pending room).encoding.words ≤ _
    omega)
theorem cutoff_time (value) : (cutoff config pending room).time value ≤ 16 * width config pending :=
  (ByteRoute.time _ _ _ _ _ _ _ _ value).trans (by have := (widths config pending room).2.2.2; omega)
theorem distribute_words : descriptionWords (distribute config pending room).code ≤ 156 * width config pending + 95 :=
  (SumContext.words _ _ _ _ _).trans (by
    change 156 * (input config pending room).encoding.words + 95 ≤ _
    have := (widths config pending room).1
    omega)
theorem successTag_words : descriptionWords (successTag config pending room).code ≤ 234 * width config pending + 53 :=
  (SumContext.mergeRight_words _ _ _ _ _).trans (by
    have := (widths config pending room).2.2.2
    change 117 * (output config pending room).encoding.words + 53 ≤ _
    omega)
theorem cutoff_words : descriptionWords (cutoff config pending room).code ≤ 52 * width config pending + 14 :=
  (ByteRoute.codeWords _ _ _ _ _ _ _ _).trans (by have := (widths config pending room).2.2.2; omega)

variable [Zero F] [DecidableEq M] [DecidableEq G]
def timeBudget := ForgeryHash.timeBudget config + 120 * width config pending + 10
def codeBudget := ForgeryHash.codeBudget config + 800 * width config pending + 400
def nameBudget := max 3 (HashCache.nameBudget config)

theorem time_bound : Interactive.TimeBoundOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (input config pending room) (code config pending room) (timeBudget config pending) := by
  have tagged := (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
    (successTag config pending room) _ (successTag_time config pending room)).on (fun _ => True)
  have success := Interactive.TimeBoundOn.seq (ForgeryHash.refines config) (ForgeryHash.time_bound config)
    tagged (fun _ _ _ _ => trivial)
  have stopped := (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
    (cutoff config pending room) _ (cutoff_time config pending room)).on (fun _ => True)
  have branches := Interactive.TimeBoundOn.dispatch (ForgeryHash.input config) (cutoffInput config pending room)
    success stopped (width_pos config.sampler.wordFits)
    (SumContext.output (ForgeryHash.forgery config).representation pending config.handler.store.representation
      config.sampler.wordFits (input config pending room).fits).fits
  have compiled := Interactive.TimeBoundOn.seq
    ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (distribute config pending room)).on (ready config))
    ((Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
      (distribute config pending room) _ (distribute_time config pending room)).on (ready config)) branches (by
        intro value valid answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        rcases value with ⟨forge | next, saved⟩ <;> exact valid)
  exact compiled.mono (by
    rw [Interactive.dispatchTime_unit]
    have := widths config pending room
    unfold timeBudget
    omega)

theorem code_bound : ((code config pending room).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    codeBudget config pending := by
  have hashed := ForgeryHash.code_bound config
  have distributed := distribute_words config pending room
  have tagged := successTag_words config pending room
  have stopped := cutoff_words config pending room
  have sizes := widths config pending room
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute,
    Interactive.dispatch_descriptionWords, successCode]
  unfold codeBudget
  omega

theorem names : WordIO.NamesAccounted ((code config pending room).lower (Fresh.port config.handler.sampler.tape))
    (nameBudget config) := by
  have distributed := (SumContext.names (ForgeryHash.forgery config).representation pending
    config.handler.store.representation config.sampler.wordFits (input config pending room).fits).mono
      (show 3 ≤ nameBudget config from Nat.le_max_left _ _)
  have tagged := (Retain.names (inr_names (Pairing.unitRepresentation w) (ForgeryHash.result config)
    config.sampler.wordFits (reply config pending room).fits).accounted
      (ForgeryHash.result config).encoding.words (reply config pending room).encoding.words
      config.handler.store.representation.encoding.words).mono (show 3 ≤ nameBudget config from Nat.le_max_left _ _)
  have stopped : NamesAccounted (cutoff config pending room).code (nameBudget config) := ByteRoute.names _ _ _ _ _ _ _ _ _
  have hashed := (ForgeryHash.names config).mono (show HashCache.nameBudget config ≤ nameBudget config from Nat.le_max_right _ _)
  exact (WordIO.NamesAccounted.compute distributed).seq
    (@Interactive.dispatch_names w Nat unifSpec (Fresh.port config.handler.sampler.tape)
      (successCode config pending room) (.compute (cutoff config pending room).code) (nameBudget config)
      (hashed.seq (.compute tagged)) (.compute stopped) _ _)

theorem buffers : ((code config pending room).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 11 := by
  have distributed := SumContext.buffers (ForgeryHash.forgery config).representation pending
    config.handler.store.representation config.sampler.wordFits (input config pending room).fits
  have tagged := SumContext.mergeRight_buffers (Pairing.unitRepresentation w) (ForgeryHash.result config)
    config.handler.store.representation config.sampler.wordFits (output config pending room).fits
  have stopped : (cutoff config pending room).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
  have hashed := ForgeryHash.buffers config
  have branches := Interactive.dispatch_buffers (Fresh.port config.handler.sampler.tape) (successCode config pending room)
    (.compute (cutoff config pending room).code) (ForgeryHash.input config).encoding.words (cutoffInput config pending room).encoding.words
  change _ ≤ max 2 (max (max ((ForgeryHash.code config).lower (Fresh.port config.handler.sampler.tape)).memBound
    (successTag config pending room).code.memBound) (cutoff config pending room).code.memBound) at branches
  change max (distribute config pending room).code.memBound _ ≤ _
  change (distribute config pending room).code.memBound ≤ 3 at distributed
  change (successTag config pending room).code.memBound ≤ 4 at tagged
  omega

theorem descriptionFits : ((code config pending room).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  .seq config.sampler.wordFits (.compute (distribute config pending room).description_fits)
    (Interactive.dispatch_descriptionFits _ _ _ _ _ config.sampler.wordFits
      (.seq config.sampler.wordFits (ForgeryHash.descriptionFits config) (.compute (successTag config pending room).description_fits))
      (.compute (cutoff config pending room).description_fits) (ForgeryHash.input config).fits (cutoffInput config pending room).fits)

theorem resources (random : RandomTape w) (value : Input config (P := P)) (valid : ready config value)
    (before : State w) (holds : (input config pending room).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code config pending room).execute (Fresh.port config.handler.sampler.tape) .unit random before)) :
    finished.time ≤ timeBudget config pending ∧
      ∃ answer ∈ support (source config value), (output config pending room).Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit random ((code config pending room).lower (Fresh.port config.handler.sampler.tape)) before finished.state
            finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            RegisterBound between (max registers ((code config pending room).lower (Fresh.port config.handler.sampler.tape)).registerSlots) ∧
            between.SupportBound (max buffers ((code config pending room).lower (Fresh.port config.handler.sampler.tape)).memBound) ∧ between.WellFormed ∧
            (((code config pending room).lower (Fresh.port config.handler.sampler.tape)).staticWords registers buffers : Int) +
              between.liveMem (max buffers ((code config pending room).lower (Fresh.port config.handler.sampler.tape)).memBound) ≤
                5 * codeBudget config pending + 4 * nameBudget config + registers + 3 * buffers + before.liveMem buffers + timeBudget config pending := by
  have stored := code_bound config pending room
  have named := names config pending room
  have allNames : WordIO.NamesBound ((code config pending room).lower (Fresh.port config.handler.sampler.tape))
      (nameBudget config + codeBudget config pending) :=
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    (refines config pending room).resources (time_bound config pending room) stored allNames random value valid before holds
      registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, result, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := bounds between visited
  exact ⟨registerBound, bufferBound, wellFormed, by push_cast at memory; omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.Terminal
