import Proofs.Runtime.Caliper.SchnorrROMTapeFreshBounds
import Proofs.Runtime.Caliper.SchnorrROMTapeReadMemory

/-! Word acceptance and complete memory accounting for fresh replay cells. Only
the scalar sampler supplies code; all private sampling and packet code is built. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Fresh
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} [Zero F] (layout : Layouts w F) (zeroValid : layout.scalar.valid 0)

theorem private_names {slots : Nat} (reserve : 3 ≤ slots) :
    WordIO.NamesAccounted ((privateCode layout zeroValid).lower (port layout)) slots := by
  have retained := Interactive.retain_names (port layout) ((natural_names layout).accounted.mono reserve) 1 1 1
  exact (WordIO.NamesAccounted.compute ((privateInput layout).names slots)).seq
    (retained.seq (WordIO.NamesAccounted.compute ((privateCell layout zeroValid).names slots)))

theorem names (sampler : Interactive.Code w) {slots : Nat}
    (scalarNames : WordIO.NamesBound (sampler.lower (port layout)) slots) :
    WordIO.NamesAccounted ((code layout zeroValid sampler).lower (port layout)) (max 3 slots) := by
  have scalar : WordIO.NamesAccounted ((scalarCode layout sampler).lower (port layout)) (max 3 slots) :=
    (WordIO.NamesAccounted.compute ((dropTag layout).names _)).seq
      ((scalarNames.accounted.mono (Nat.le_max_right _ _)).seq
        (WordIO.NamesAccounted.compute ((scalarCell layout).names _)))
  have dispatched := Interactive.dispatch_names (port layout) scalar (private_names layout zeroValid (Nat.le_max_left 3 slots)) 1 1
  exact (WordIO.NamesAccounted.compute ((selector layout).names _)).seq dispatched

theorem private_descriptionFits : ((privateCode layout zeroValid).lower (port layout)).DescriptionFits := by
  have nameFits : Interactive.savedBuffer (port layout) (naturalCode layout) < 2 ^ w := by
    have bound := natural_buffers layout
    have width := layout.wordFits
    dsimp only [Interactive.savedBuffer]
    omega
  have retained := Interactive.retain_descriptionFits (port layout) (naturalCode layout)
    (Interactive.savedBuffer (port layout) (naturalCode layout)) 1 1 1 layout.wordFits (natural_fits layout)
    nameFits (by have := layout.wordFits; omega) (by have := layout.wordFits; omega)
    (by have := layout.wordFits; omega)
  exact .seq layout.wordFits (.compute (privateInput layout).implementation.program.description_fits)
    (.seq layout.wordFits retained (.compute (privateCell layout zeroValid).implementation.program.description_fits))

theorem descriptionFits (sampler : Interactive.Code w) (scalarFits : (sampler.lower (port layout)).DescriptionFits) :
    ((code layout zeroValid sampler).lower (port layout)).DescriptionFits := by
  have scalar : ((scalarCode layout sampler).lower (port layout)).DescriptionFits :=
    .seq layout.wordFits (.compute (dropTag layout).implementation.program.description_fits)
      (.seq layout.wordFits scalarFits (.compute (scalarCell layout).implementation.program.description_fits))
  have dispatched := Interactive.dispatch_descriptionFits (port layout) (scalarCode layout sampler) (privateCode layout zeroValid)
    1 1 layout.wordFits scalar (private_descriptionFits layout zeroValid)
    (by have := layout.wordFits; omega) (by have := layout.wordFits; omega)
  exact .seq layout.wordFits (.compute (selector layout).implementation.program.description_fits) dispatched

theorem private_buffers : ((privateCode layout zeroValid).lower (port layout)).memBound ≤ 4 := by
  have retained := Interactive.retain_buffers (port layout) (naturalCode layout) 1 1 1
  change ((privateDrawCode layout).lower (port layout)).memBound ≤ _ at retained
  have drawn := natural_buffers layout
  have prepared := (privateInput layout).buffers_le
  have finished := (privateCell layout zeroValid).buffers_le
  rw [privateInput_buffers] at prepared
  rw [privateCell_buffers] at finished
  change max (privateInput layout).implementation.program.code.memBound
    (max ((privateDrawCode layout).lower (port layout)).memBound (privateCell layout zeroValid).implementation.program.code.memBound) ≤ 4
  omega

theorem buffers (sampler : Interactive.Code w) :
    ((code layout zeroValid sampler).lower (port layout)).memBound ≤ max 4 (sampler.lower (port layout)).memBound := by
  have selected := (selector layout).buffers_le
  have dropped : (dropTag layout).implementation.program.code.memBound ≤ 2 := (dropTag layout).buffers_le
  have cell := (scalarCell layout).buffers_le
  rw [selector_buffers] at selected
  rw [scalarCell_buffers] at cell
  have privateBound := private_buffers layout zeroValid
  have scalarBound : ((scalarCode layout sampler).lower (port layout)).memBound ≤ max 4 (sampler.lower (port layout)).memBound := by
    change max (dropTag layout).implementation.program.code.memBound
      (max (sampler.lower (port layout)).memBound (scalarCell layout).implementation.program.code.memBound) ≤ _
    omega
  have dispatched := Interactive.dispatch_buffers (port layout) (scalarCode layout sampler) (privateCode layout zeroValid) 1 1
  change ((branchCode layout zeroValid sampler).lower (port layout)).memBound ≤ _ at dispatched
  change max (selector layout).implementation.program.code.memBound ((branchCode layout zeroValid sampler).lower (port layout)).memBound ≤ _
  omega

theorem resources {scalarSource : ProbComp layout.scalar.Value} {sampler : Interactive.Code w}
    (scalarCorrect : Interactive.Refines (port layout) .unit layout.unit.representation layout.scalar.representation
      (fun _ => scalarSource) sampler) {samplerTime samplerWords slots : Nat}
    (scalarTimeBound : Interactive.TimeBound (port layout) .unit layout.unit.representation sampler samplerTime)
    (scalarWordsBound : (sampler.lower (port layout)).descriptionWords ≤ samplerWords)
    (scalarNames : WordIO.NamesBound (sampler.lower (port layout)) slots)
    (tape : RandomTape w) (tag : layout.counter.Value) (before : State w) (holds : layout.counter.representation.Holds tag before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w) (reached : some finished ∈ support ((code layout zeroValid sampler).execute (port layout) .unit tape before)) :
    finished.time ≤ timeBudget layout zeroValid samplerTime ∧
    ∃ answer ∈ support (denote layout zeroValid scalarSource tag), layout.entry.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((code layout zeroValid sampler).lower (port layout)) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((code layout zeroValid sampler).lower (port layout)).registerSlots) ∧
          between.SupportBound (max buffers ((code layout zeroValid sampler).lower (port layout)).memBound) ∧ between.WellFormed ∧
          (((code layout zeroValid sampler).lower (port layout)).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code layout zeroValid sampler).lower (port layout)).memBound) ≤
              5 * codeBudget layout zeroValid samplerWords + 4 * max 3 slots + registers + 3 * buffers +
                before.liveMem buffers + timeBudget layout zeroValid samplerTime := by
  have stored := code_bound layout zeroValid sampler scalarWordsBound
  have accounted := names layout zeroValid sampler scalarNames
  have reserved : WordIO.NamesBound ((code layout zeroValid sampler).lower (port layout))
      (max 3 slots + codeBudget layout zeroValid samplerWords) :=
    ⟨accounted.registers.trans (Nat.add_le_add_left stored _),
      accounted.buffers.trans (Nat.add_le_add_left stored _)⟩
  have result := (refines layout zeroValid scalarCorrect).resources (time_bound layout zeroValid scalarCorrect scalarTimeBound)
    stored reserved tape tag before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨elapsed, answer, supported, output, execution, visitedBound⟩ := result
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := visitedBound between visited
  refine ⟨registerBound, bufferBound, wellFormed, ?_⟩
  push_cast at memory
  omega

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Fresh
