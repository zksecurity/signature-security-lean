import Signatures.Runtime.Caliper.SchnorrROMTapeReadBounds
import Signatures.Runtime.Caliper.CacheReadBuffers

/-! Address acceptance, scratch extent and complete visited-state memory for
the constructed replay handler. Static storage includes its actual code. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Read
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F I : Type} {spec : OracleSpec I}
    (layout : Layouts w F) (port : Interactive.Port w spec) (draw : Interactive.Code w)

theorem names {slots : Nat} (drawNames : WordIO.NamesBound (draw.lower port) slots) :
    WordIO.NamesAccounted ((code layout port draw).lower port) slots := by
  have retained := Interactive.retain_names port drawNames.accounted
    layout.counter.representation.encoding.words layout.entry.representation.encoding.words
    (frame layout).representation.encoding.words
  have miss := (WordIO.NamesAccounted.compute ((request layout).names slots)).seq
    (retained.seq (WordIO.NamesAccounted.compute ((finish layout).names slots)))
  have branch : WordIO.NamesAccounted ((branchCode layout port draw).lower port) slots :=
    @Interactive.dispatch_names w I spec port (.compute (hit layout).implementation.program.code)
      (missCode layout port draw) slots (WordIO.NamesAccounted.compute ((hit layout).names slots)) miss
    (frame layout).representation.encoding.words (frame layout).representation.encoding.words
  exact (WordIO.NamesAccounted.compute ((choose layout).names slots)).seq branch

theorem descriptionFits_of_buffers (drawFits : (draw.lower port).DescriptionFits)
    (bufferFits : (draw.lower port).memBound < 2 ^ w) :
    ((code layout port draw).lower port).DescriptionFits := by
  have nameFits : Interactive.savedBuffer port draw < 2 ^ w := by
    have width := layout.wordFits
    dsimp only [Interactive.savedBuffer]
    omega
  have retained := Interactive.retain_descriptionFits port draw (Interactive.savedBuffer port draw)
    layout.counter.representation.encoding.words layout.entry.representation.encoding.words
    (frame layout).representation.encoding.words layout.wordFits drawFits nameFits
    layout.counter.representation.fits (frame layout).representation.fits (drawn layout).representation.fits
  have miss := WordIO.Code.DescriptionFits.seq layout.wordFits
    (.compute (request layout).implementation.program.description_fits)
    (.seq layout.wordFits retained (.compute (finish layout).implementation.program.description_fits))
  have branch := Interactive.dispatch_descriptionFits port (.compute (hit layout).implementation.program.code)
    (missCode layout port draw) _ _ layout.wordFits
    (.compute (hit layout).implementation.program.description_fits) miss
    (frame layout).representation.fits (frame layout).representation.fits
  exact .seq layout.wordFits (.compute (choose layout).implementation.program.description_fits) branch

theorem descriptionFits (drawFits : (draw.lower port).DescriptionFits) {slots : Nat}
    (drawNames : WordIO.NamesBound (draw.lower port) slots) (slotsFit : slots < 2 ^ w) :
    ((code layout port draw).lower port).DescriptionFits :=
  descriptionFits_of_buffers layout port draw drawFits (drawNames.buffers.trans_lt slotsFit)

theorem buffers : ((code layout port draw).lower port).memBound ≤ max 7 ((draw.lower port).memBound + 1) := by
  have retained := Interactive.retain_buffers port draw layout.counter.representation.encoding.words
    layout.entry.representation.encoding.words (frame layout).representation.encoding.words
  change ((drawCode layout port draw).lower port).memBound ≤ _ at retained
  have chosen := (choose layout).buffers_le
  have hitBound := (hit layout).buffers_le
  have requestBound := (request layout).buffers_le
  have finishBound := (finish layout).buffers_le
  rw [choose_buffers] at chosen
  rw [hit_buffers] at hitBound
  rw [request_buffers] at requestBound
  rw [finish_buffers] at finishBound
  have dispatched := Interactive.dispatch_buffers port (.compute (hit layout).implementation.program.code)
    (missCode layout port draw) (frame layout).representation.encoding.words (frame layout).representation.encoding.words
  change ((branchCode layout port draw).lower port).memBound ≤ max 2 (max (hit layout).implementation.program.code.memBound
    (max (request layout).implementation.program.code.memBound
      (max ((drawCode layout port draw).lower port).memBound (finish layout).implementation.program.code.memBound))) at dispatched
  change max (choose layout).implementation.program.code.memBound ((branchCode layout port draw).lower port).memBound ≤ _
  omega

/-- Source result, time and all intermediate memory bounds concern the same
execution and the same adaptive oracle replies. -/
theorem resources {drawSource : layout.counter.Value → OracleComp spec layout.entry.Value}
    (drawCorrect : Interactive.Refines port .unit layout.counter.representation layout.entry.representation drawSource draw)
    {drawTime drawWords slots : Nat}
    (drawTimeBound : Interactive.TimeBound port .unit layout.counter.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords)
    (drawNames : WordIO.NamesBound (draw.lower port) slots)
    (tape : RandomTape w) (value : (input layout).Value) (before : State w)
    (holds : (input layout).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w) (reached : some finished ∈ support ((code layout port draw).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout drawTime ∧
    ∃ answer ∈ support (denote layout drawSource value), (output layout).representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((code layout port draw).lower port) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((code layout port draw).lower port).registerSlots) ∧
          between.SupportBound (max buffers ((code layout port draw).lower port).memBound) ∧ between.WellFormed ∧
          (((code layout port draw).lower port).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code layout port draw).lower port).memBound) ≤
              5 * codeBudget layout drawWords + 4 * slots + registers + 3 * buffers +
                before.liveMem buffers + timeBudget layout drawTime := by
  have stored := code_bound layout port draw drawWordsBound
  have accounted := names layout port draw drawNames
  have reserved : WordIO.NamesBound ((code layout port draw).lower port) (slots + codeBudget layout drawWords) :=
    ⟨accounted.registers.trans (Nat.add_le_add_left stored slots),
      accounted.buffers.trans (Nat.add_le_add_left stored slots)⟩
  have result := (refines drawCorrect).resources (time_bound layout port drawCorrect drawTimeBound)
    stored reserved tape value before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨elapsed, answer, supported, output, execution, visitedBound⟩ := result
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := visitedBound between visited
  refine ⟨registerBound, bufferBound, wellFormed, ?_⟩
  push_cast at memory
  omega

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Read
