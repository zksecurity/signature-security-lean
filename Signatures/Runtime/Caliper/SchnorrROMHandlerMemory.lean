import Signatures.Runtime.Caliper.SchnorrROMHandlerBounds

/-! Dense names, stored-word acceptance and memory at every visited state for
the complete dispatched execution. The same execution witnesses correctness,
time and memory; every inactive branch still contributes stored code. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (ops : Operations config)

omit [SMul F G] [Sub G] [Zero F] [DecidableEq M] [DecidableEq G] in
theorem tag_names : NamesBound (randomTag config).code 3 ∧ NamesBound (hashTag config).code 3 ∧
    NamesBound (signingTag config).code 3 := by
  have outerLeft := inl_names (innerOutput config) config.handler.output.representation config.sampler.wordFits (output config).fits
  have outerRight := inr_names (innerOutput config) config.handler.output.representation config.sampler.wordFits (output config).fits
  have innerLeft := inl_names (Random.output config).representation (Hash.output config).representation
    config.sampler.wordFits (innerOutput config).fits
  have innerRight := inr_names (Random.output config).representation (Hash.output config).representation
    config.sampler.wordFits (innerOutput config).fits
  exact ⟨⟨max_le innerLeft.registers outerLeft.registers, max_le innerLeft.buffers outerLeft.buffers⟩,
    ⟨max_le innerRight.registers outerLeft.registers, max_le innerRight.buffers outerLeft.buffers⟩, outerRight⟩

def nameBudget := max 3 (max (max (Random.nameBudget config) (Hash.nameBudget config))
  (Signing.Handler.nameBudget config.handler trivial 3 ops.slots))

theorem names : WordIO.NamesAccounted ((code config ops).lower (Fresh.port config.handler.sampler.tape))
    (nameBudget config ops) := by
  have rt := (tag_names config).1.accounted.mono (show 3 ≤ nameBudget config ops from Nat.le_max_left 3 _)
  have ht := (tag_names config).2.1.accounted.mono (show 3 ≤ nameBudget config ops from Nat.le_max_left 3 _)
  have st := (tag_names config).2.2.accounted.mono (show 3 ≤ nameBudget config ops from Nat.le_max_left 3 _)
  have random := (Random.names config).mono (show Random.nameBudget config ≤ nameBudget config ops by unfold nameBudget; omega)
  have hashed := (Hash.names config).mono (show Hash.nameBudget config ≤ nameBudget config ops by unfold nameBudget; omega)
  have signed := (Signing.Enumerated.names config ops.scale ops.sub ops.scaleNames.buffers ops.subNames.buffers ops.reserve
    ops.slots ops.scaleNames.accounted ops.subNames.accounted).mono
      (show Signing.Handler.nameBudget config.handler trivial 3 ops.slots ≤ nameBudget config ops by unfold nameBudget; omega)
  exact @Interactive.dispatch_names w Nat unifSpec (Fresh.port config.handler.sampler.tape)
    (innerCode config) (signingCode config ops) (nameBudget config ops)
    (@Interactive.dispatch_names w Nat unifSpec (Fresh.port config.handler.sampler.tape)
      (randomCode config) (hashCode config) (nameBudget config ops)
      (random.seq (.compute rt)) (hashed.seq (.compute ht)) _ _)
    (signed.seq (.compute st)) _ _

theorem buffers : ((code config ops).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ max 12 (ops.slots + 3) := by
  have random := Random.buffers config
  have hashed := Hash.buffers config
  have signed := Signing.Enumerated.buffers config ops.scale ops.sub ops.scaleNames.buffers ops.subNames.buffers ops.reserve
  change ((signCode config ops).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ _ at signed
  have tags := tag_names config
  have inner := Interactive.dispatch_buffers (Fresh.port config.handler.sampler.tape) (randomCode config) (hashCode config)
    (Random.input config).representation.encoding.words (Hash.input config).representation.encoding.words
  have combined := Interactive.dispatch_buffers (Fresh.port config.handler.sampler.tape) (innerCode config) (signingCode config ops)
    (innerInput config).encoding.words config.handler.input.representation.encoding.words
  change ((innerCode config).lower (Fresh.port config.handler.sampler.tape)).memBound ≤
    max 2 (max (max ((Random.code config).lower (Fresh.port config.handler.sampler.tape)).memBound (randomTag config).code.memBound)
      (max ((Hash.code config).lower (Fresh.port config.handler.sampler.tape)).memBound (hashTag config).code.memBound)) at inner
  change ((code config ops).lower (Fresh.port config.handler.sampler.tape)).memBound ≤
    max 2 (max ((innerCode config).lower (Fresh.port config.handler.sampler.tape)).memBound
      (max ((signCode config ops).lower (Fresh.port config.handler.sampler.tape)).memBound (signingTag config).code.memBound)) at combined
  have := tags.1.buffers; have := tags.2.1.buffers; have := tags.2.2.buffers
  omega

theorem descriptionFits : ((code config ops).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  Interactive.dispatch_descriptionFits _ _ _ _ _ config.sampler.wordFits
    (Interactive.dispatch_descriptionFits _ _ _ _ _ config.sampler.wordFits
      (.seq config.sampler.wordFits (Random.descriptionFits config) (.compute (randomTag config).description_fits))
      (.seq config.sampler.wordFits (Hash.descriptionFits config) (.compute (hashTag config).description_fits))
      (Random.input config).representation.fits (Hash.input config).representation.fits)
    (.seq config.sampler.wordFits
      (Signing.Enumerated.descriptionFits config ops.scale ops.sub ops.scaleNames.buffers ops.subNames.buffers ops.reserve)
      (.compute (signingTag config).description_fits))
    (innerInput config).fits config.handler.input.representation.fits

theorem resources (budget : Budget config ops) (random : RandomTape w) (value : Input config) (valid : ready config value)
    (before : State w) (holds : (input config).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code config ops).execute (Fresh.port config.handler.sampler.tape) .unit random before)) :
    finished.time ≤ timeBudget config ops budget ∧
      ∃ answer ∈ support (source config ops value), (output config).Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit random ((code config ops).lower (Fresh.port config.handler.sampler.tape)) before finished.state
            finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            RegisterBound between (max registers ((code config ops).lower (Fresh.port config.handler.sampler.tape)).registerSlots) ∧
            between.SupportBound (max buffers ((code config ops).lower (Fresh.port config.handler.sampler.tape)).memBound) ∧ between.WellFormed ∧
            (((code config ops).lower (Fresh.port config.handler.sampler.tape)).staticWords registers buffers : Int) +
              between.liveMem (max buffers ((code config ops).lower (Fresh.port config.handler.sampler.tape)).memBound) ≤
                5 * codeBudget config ops budget + 4 * nameBudget config ops + registers + 3 * buffers +
                  before.liveMem buffers + timeBudget config ops budget := by
  have stored := code_bound config ops budget
  have named := names config ops
  have allNames : WordIO.NamesBound ((code config ops).lower (Fresh.port config.handler.sampler.tape))
      (nameBudget config ops + codeBudget config ops budget) :=
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    (refines config ops).resources (time_bound config ops budget) stored allNames
      random value valid before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, result, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := bounds between visited
  exact ⟨registerBound, bufferBound, wellFormed, by push_cast at memory; omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
