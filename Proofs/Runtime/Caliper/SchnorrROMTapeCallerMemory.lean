import Proofs.Runtime.Caliper.SchnorrROMTapeCallerBounds

/-! Complete address, stored-code and visited-memory bounds for caller replay
queries. Resource premises describe only the local scalar sampler. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Caller
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} [Zero F] (layout : Layouts w F) (zeroValid : layout.scalar.valid 0)

def nameSlots (samplerWords slots : Nat) : Nat := max 3 slots + Fresh.codeBudget layout zeroValid samplerWords

theorem query_names (sampler : Interactive.Code w) {samplerWords slots : Nat}
    (scalarWords : (sampler.lower (Fresh.port layout)).descriptionWords ≤ samplerWords)
    (scalarNames : WordIO.NamesBound (sampler.lower (Fresh.port layout)) slots) :
    WordIO.NamesAccounted ((Query.code layout zeroValid sampler).lower (Fresh.port layout))
      (nameSlots layout zeroValid samplerWords slots) := by
  have stored := Fresh.code_bound layout zeroValid sampler scalarWords
  have accounted := Fresh.names layout zeroValid sampler scalarNames
  have reserved : WordIO.NamesBound ((Fresh.code layout zeroValid sampler).lower (Fresh.port layout))
      (nameSlots layout zeroValid samplerWords slots) :=
    ⟨accounted.registers.trans (Nat.add_le_add_left stored _), accounted.buffers.trans (Nat.add_le_add_left stored _)⟩
  exact Read.names layout (Fresh.port layout) (Fresh.code layout zeroValid sampler) reserved

theorem private_names (sampler : Interactive.Code w) {samplerWords slots : Nat}
    (scalarWords : (sampler.lower (Fresh.port layout)).descriptionWords ≤ samplerWords)
    (scalarNames : WordIO.NamesBound (sampler.lower (Fresh.port layout)) slots) :
    WordIO.NamesAccounted ((privateCode layout zeroValid sampler).lower (Fresh.port layout))
      (nameSlots layout zeroValid samplerWords slots) := by
  have retained := Interactive.retain_names (Fresh.port layout) (query_names layout zeroValid sampler scalarWords scalarNames)
    (Read.input layout).representation.encoding.words (Read.output layout).representation.encoding.words
    (Reply.range layout).representation.encoding.words
  exact (WordIO.NamesAccounted.compute ((prepare layout zeroValid).names _)).seq
    (retained.seq (WordIO.NamesAccounted.compute ((finish layout).names _)))

theorem scalar_names (sampler : Interactive.Code w) {samplerWords slots : Nat}
    (scalarWords : (sampler.lower (Fresh.port layout)).descriptionWords ≤ samplerWords)
    (scalarNames : WordIO.NamesBound (sampler.lower (Fresh.port layout)) slots) :
    WordIO.NamesAccounted ((scalarCode layout zeroValid sampler).lower (Fresh.port layout))
      (nameSlots layout zeroValid samplerWords slots) :=
  (WordIO.NamesAccounted.compute ((scalarPacket layout zeroValid).names _)).seq
    ((query_names layout zeroValid sampler scalarWords scalarNames).seq
      (WordIO.NamesAccounted.compute ((Reply.scalarDecoder layout).names _)))

theorem private_buffers (sampler : Interactive.Code w) :
    ((privateCode layout zeroValid sampler).lower (Fresh.port layout)).memBound ≤
      max 8 ((sampler.lower (Fresh.port layout)).memBound + 2) := by
  have queried := Query.buffers layout zeroValid sampler
  have retained := Interactive.retain_buffers (Fresh.port layout) (Query.code layout zeroValid sampler)
    (Read.input layout).representation.encoding.words (Read.output layout).representation.encoding.words
    (Reply.range layout).representation.encoding.words
  change ((retainedCode layout zeroValid sampler).lower (Fresh.port layout)).memBound ≤ _ at retained
  have prepared := (prepare layout zeroValid).buffers_le
  rw [prepare_buffers] at prepared
  have finished := (finish layout).buffers_le
  rw [finish_buffers] at finished
  change max (prepare layout zeroValid).implementation.program.code.memBound
    (max ((retainedCode layout zeroValid sampler).lower (Fresh.port layout)).memBound
      (finish layout).implementation.program.code.memBound) ≤ _
  omega

theorem scalar_buffers (sampler : Interactive.Code w) :
    ((scalarCode layout zeroValid sampler).lower (Fresh.port layout)).memBound ≤
      max 7 ((sampler.lower (Fresh.port layout)).memBound + 1) := by
  have queried := Query.buffers layout zeroValid sampler
  have prepared := (scalarPacket layout zeroValid).buffers_le
  rw [scalarPacket_buffers] at prepared
  have finished := (Reply.scalarDecoder layout).buffers_le
  rw [Reply.scalar_buffers] at finished
  change max (scalarPacket layout zeroValid).implementation.program.code.memBound
    (max ((Query.code layout zeroValid sampler).lower (Fresh.port layout)).memBound
      (Reply.scalarDecoder layout).implementation.program.code.memBound) ≤ _
  omega

theorem private_descriptionFits (sampler : Interactive.Code w)
    (scalarFits : (sampler.lower (Fresh.port layout)).DescriptionFits)
    (bufferFits : (sampler.lower (Fresh.port layout)).memBound + 1 < 2 ^ w) :
    ((privateCode layout zeroValid sampler).lower (Fresh.port layout)).DescriptionFits := by
  have queried := Query.descriptionFits layout zeroValid sampler scalarFits (by omega)
  have nameFits : Interactive.savedBuffer (Fresh.port layout) (Query.code layout zeroValid sampler) < 2 ^ w := by
    have bounded := Query.buffers layout zeroValid sampler
    have width := layout.wordFits
    dsimp only [Interactive.savedBuffer]
    omega
  have retained := Interactive.retain_descriptionFits (Fresh.port layout) (Query.code layout zeroValid sampler)
    (Interactive.savedBuffer (Fresh.port layout) (Query.code layout zeroValid sampler))
    (Read.input layout).representation.encoding.words (Read.output layout).representation.encoding.words
    (Reply.range layout).representation.encoding.words layout.wordFits queried nameFits
    (Read.input layout).representation.fits (Reply.range layout).representation.fits (retainedOutput layout).representation.fits
  exact .seq layout.wordFits (.compute (prepare layout zeroValid).implementation.program.description_fits)
    (.seq layout.wordFits retained (.compute (finish layout).implementation.program.description_fits))

theorem scalar_descriptionFits (sampler : Interactive.Code w)
    (scalarFits : (sampler.lower (Fresh.port layout)).DescriptionFits)
    (bufferFits : (sampler.lower (Fresh.port layout)).memBound < 2 ^ w) :
    ((scalarCode layout zeroValid sampler).lower (Fresh.port layout)).DescriptionFits :=
  .seq layout.wordFits (.compute (scalarPacket layout zeroValid).implementation.program.description_fits)
    (.seq layout.wordFits (Query.descriptionFits layout zeroValid sampler scalarFits bufferFits)
      (.compute (Reply.scalarDecoder layout).implementation.program.description_fits))

variable {scalarSource : ProbComp layout.scalar.Value} {sampler : Interactive.Code w}
    (scalarCorrect : Interactive.Refines (Fresh.port layout) .unit layout.unit.representation layout.scalar.representation
      (fun _ => scalarSource) sampler)

include scalarCorrect in
theorem private_resources {samplerTime samplerWords slots : Nat}
    (scalarTimeBound : Interactive.TimeBound (Fresh.port layout) .unit layout.unit.representation sampler samplerTime)
    (scalarWordsBound : (sampler.lower (Fresh.port layout)).descriptionWords ≤ samplerWords)
    (scalarNames : WordIO.NamesBound (sampler.lower (Fresh.port layout)) slots)
    (tape : RandomTape w) (value : (privateInput layout).Value) (before : State w)
    (holds : (privateInput layout).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w) (reached : some finished ∈ support ((privateCode layout zeroValid sampler).execute (Fresh.port layout) .unit tape before)) :
    finished.time ≤ privateTime layout zeroValid samplerTime ∧
    ∃ answer ∈ support (privateDenote layout zeroValid scalarSource value), (Reply.privateOutput layout).representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((privateCode layout zeroValid sampler).lower (Fresh.port layout)) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((privateCode layout zeroValid sampler).lower (Fresh.port layout)).registerSlots) ∧
          between.SupportBound (max buffers ((privateCode layout zeroValid sampler).lower (Fresh.port layout)).memBound) ∧ between.WellFormed ∧
          (((privateCode layout zeroValid sampler).lower (Fresh.port layout)).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((privateCode layout zeroValid sampler).lower (Fresh.port layout)).memBound) ≤
              5 * privateWords layout zeroValid samplerWords + 4 * nameSlots layout zeroValid samplerWords slots +
                registers + 3 * buffers + before.liveMem buffers + privateTime layout zeroValid samplerTime := by
  have stored := private_words layout zeroValid sampler scalarWordsBound
  have accounted := private_names layout zeroValid sampler scalarWordsBound scalarNames
  have reserved : WordIO.NamesBound ((privateCode layout zeroValid sampler).lower (Fresh.port layout))
      (nameSlots layout zeroValid samplerWords slots + privateWords layout zeroValid samplerWords) :=
    ⟨accounted.registers.trans (Nat.add_le_add_left stored _), accounted.buffers.trans (Nat.add_le_add_left stored _)⟩
  have result := (private_refines layout zeroValid scalarCorrect).resources (private_time layout zeroValid scalarCorrect scalarTimeBound)
    stored reserved tape value before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨elapsed, answer, supported, output, execution, visitedBound⟩ := result
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := visitedBound between visited
  exact ⟨registerBound, bufferBound, wellFormed, by push_cast at memory; omega⟩

include scalarCorrect in
theorem scalar_resources {samplerTime samplerWords slots : Nat}
    (scalarTimeBound : Interactive.TimeBound (Fresh.port layout) .unit layout.unit.representation sampler samplerTime)
    (scalarWordsBound : (sampler.lower (Fresh.port layout)).descriptionWords ≤ samplerWords)
    (scalarNames : WordIO.NamesBound (sampler.lower (Fresh.port layout)) slots)
    (tape : RandomTape w) (value : (Read.store layout).Value) (before : State w)
    (holds : (Read.store layout).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w) (reached : some finished ∈ support ((scalarCode layout zeroValid sampler).execute (Fresh.port layout) .unit tape before)) :
    finished.time ≤ scalarTime layout zeroValid samplerTime ∧
    ∃ answer ∈ support (scalarDenote layout zeroValid scalarSource value), (Reply.scalarOutput layout).representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((scalarCode layout zeroValid sampler).lower (Fresh.port layout)) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((scalarCode layout zeroValid sampler).lower (Fresh.port layout)).registerSlots) ∧
          between.SupportBound (max buffers ((scalarCode layout zeroValid sampler).lower (Fresh.port layout)).memBound) ∧ between.WellFormed ∧
          (((scalarCode layout zeroValid sampler).lower (Fresh.port layout)).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((scalarCode layout zeroValid sampler).lower (Fresh.port layout)).memBound) ≤
              5 * scalarWords layout zeroValid samplerWords + 4 * nameSlots layout zeroValid samplerWords slots +
                registers + 3 * buffers + before.liveMem buffers + scalarTime layout zeroValid samplerTime := by
  have stored := scalar_words layout zeroValid sampler scalarWordsBound
  have accounted := scalar_names layout zeroValid sampler scalarWordsBound scalarNames
  have reserved : WordIO.NamesBound ((scalarCode layout zeroValid sampler).lower (Fresh.port layout))
      (nameSlots layout zeroValid samplerWords slots + scalarWords layout zeroValid samplerWords) :=
    ⟨accounted.registers.trans (Nat.add_le_add_left stored _), accounted.buffers.trans (Nat.add_le_add_left stored _)⟩
  have result := (scalar_refines layout zeroValid scalarCorrect).resources (scalar_time layout zeroValid scalarCorrect scalarTimeBound)
    stored reserved tape value before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨elapsed, answer, supported, output, execution, visitedBound⟩ := result
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := visitedBound between visited
  exact ⟨registerBound, bufferBound, wellFormed, by push_cast at memory; omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Caller
