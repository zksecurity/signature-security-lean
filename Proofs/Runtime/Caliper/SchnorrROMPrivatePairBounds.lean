import Proofs.Runtime.Caliper.SchnorrROMPrivatePairReplay

/-! Costs of the two stateful private draws, including both sampler bodies,
retention of the first scalar, executed permutations and every visited state. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Pair
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F C : Type} [Zero F] (layout : Layouts w F C)
    (caller : Caller layout) (zeroValid : layout.tape.scalar.valid 0)

def overhead := 8 * (Read.tapes layout.tape).representation.encoding.words +
  24 * (Reply.scalarOutput layout.tape).representation.encoding.words + 20 * layout.tape.scalar.representation.encoding.words
def timeBudget (localTime initialTime fuel : Nat) :=
  2 * Service.timeBudget layout zeroValid localTime initialTime fuel + overhead layout
def codeBudget (fuel : Nat) := 2 * Service.codeBudget layout caller zeroValid fuel +
  26 * (Read.tapes layout.tape).representation.encoding.words +
  78 * (Reply.scalarOutput layout.tape).representation.encoding.words + 65 * layout.tape.scalar.representation.encoding.words + 74

theorem retained_refines (fuel : Nat) :
    Interactive.RefinesOn (fun value => Service.ready layout fuel value.1) (Fresh.port layout.tape) .unit
      ((Read.tapes layout.tape).representation.prod layout.tape.scalar.representation (by
        have := (Reply.scalarOutput layout.tape).representation.fits
        change layout.tape.scalar.representation.encoding.words + (Read.tapes layout.tape).representation.encoding.words < 2 ^ w at this
        omega))
      ((Reply.scalarOutput layout.tape).representation.prod layout.tape.scalar.representation (by have := outputFits layout; omega))
      (fun value => (fun answer => (answer, value.2)) <$> Service.source layout caller zeroValid fuel value.1)
      (retained layout caller zeroValid fuel) :=
  (Service.refines layout caller zeroValid fuel).retain (by decide) layout.tape.scalar.representation layout.tape.wordFits _ _

theorem continuation_time (fuel localTime initialTime : Nat)
    (localBound : ∀ value, caller.continuation.time value ≤ localTime)
    (initialBound : ∀ value, caller.initialCode.time value ≤ initialTime) :
    Interactive.TimeBoundOn (nextReady layout fuel) (Fresh.port layout.tape) .unit
      (Reply.scalarOutput layout.tape).representation (continuation layout caller zeroValid fuel)
      (Service.timeBudget layout zeroValid localTime initialTime fuel + overhead layout) := by
  have retainedBound := (Interactive.TimeBoundOn.retain (Service.refines layout caller zeroValid fuel)
    (Service.time_bound layout caller zeroValid fuel localTime initialTime localBound initialBound)
    (by decide) layout.tape.scalar.representation layout.tape.wordFits (by
      have := (Reply.scalarOutput layout.tape).representation.fits
      change layout.tape.scalar.representation.encoding.words + (Read.tapes layout.tape).representation.encoding.words < 2 ^ w at this
      omega)).mono (Interactive.retain_time_unit_le _ _ _ _ _)
  have finishBound := (Interactive.TimeBound.compute (port := Fresh.port layout.tape) (cost := .unit) (finish layout)
    (8 * ((Reply.scalarOutput layout.tape).representation.encoding.words + layout.tape.scalar.representation.encoding.words))
    (Pairing.swap_time_unit_le _ _ layout.tape.wordFits (by have := outputFits layout; omega))).on (fun _ => True)
  have tailBound := Interactive.TimeBoundOn.seq (retained_refines layout caller zeroValid fuel) retainedBound finishBound (by intros; trivial)
  have prepareBound := (Interactive.TimeBound.compute (port := Fresh.port layout.tape) (cost := .unit) (prepare layout)
    (8 * (layout.tape.scalar.representation.encoding.words + (Read.tapes layout.tape).representation.encoding.words))
    (fun value => Pairing.swap_time_unit_le _ _ layout.tape.wordFits
      (Reply.scalarOutput layout.tape).representation.fits (unpack layout value))).on (nextReady layout fuel)
  have combined := Interactive.TimeBoundOn.seq
    ((Interactive.Refines.compute (Fresh.port layout.tape) .unit (prepare layout)).on (nextReady layout fuel))
    prepareBound tailBound (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact valid)
  apply combined.mono
  have sizes : (Reply.scalarOutput layout.tape).representation.encoding.words =
    layout.tape.scalar.representation.encoding.words + (Read.tapes layout.tape).representation.encoding.words := rfl
  unfold overhead
  change _ ≤ _ + (8 * _ + 24 * (layout.tape.scalar.representation.encoding.words +
    (Read.tapes layout.tape).representation.encoding.words) + 20 * _)
  omega

theorem time_bound (fuel localTime initialTime : Nat)
    (localBound : ∀ value, caller.continuation.time value ≤ localTime)
    (initialBound : ∀ value, caller.initialCode.time value ≤ initialTime) :
    Interactive.TimeBoundOn (ready layout fuel) (Fresh.port layout.tape) .unit (Read.tapes layout.tape).representation
      (code layout caller zeroValid fuel) (timeBudget layout zeroValid localTime initialTime fuel) := by
  have first : Interactive.RefinesOn (ready layout fuel) (Fresh.port layout.tape) .unit
      (Read.tapes layout.tape).representation (Reply.scalarOutput layout.tape).representation
      (Service.source layout caller zeroValid fuel) (Service.code layout caller zeroValid fuel) :=
    fun tape saved valid before holds => Service.refines layout caller zeroValid fuel tape saved
      (first_ready layout fuel saved valid) before holds
  have firstTime : Interactive.TimeBoundOn (ready layout fuel) (Fresh.port layout.tape) .unit
      (Read.tapes layout.tape).representation (Service.code layout caller zeroValid fuel)
      (Service.timeBudget layout zeroValid localTime initialTime fuel) :=
    fun tape saved valid before holds finished reached =>
      Service.time_bound layout caller zeroValid fuel localTime initialTime localBound initialBound
        tape saved (first_ready layout fuel saved valid) before holds finished reached
  exact (Interactive.TimeBoundOn.seq first firstTime
    (continuation_time layout caller zeroValid fuel localTime initialTime localBound initialBound)
    (second_ready layout caller zeroValid fuel)).mono (by unfold timeBudget; omega)

theorem code_bound (fuel : Nat) :
    ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).descriptionWords ≤ codeBudget layout caller zeroValid fuel := by
  have body := Service.code_bound layout caller zeroValid fuel
  have prepared := Pairing.swap_descriptionWords_le .unit (by decide) layout.tape.scalar.representation
    (Read.tapes layout.tape).representation layout.tape.wordFits (Reply.scalarOutput layout.tape).representation.fits
  change descriptionWords (prepare layout).code ≤ _ at prepared
  have finished := Pairing.swap_descriptionWords_le .unit (by decide) (Reply.scalarOutput layout.tape).representation
    layout.tape.scalar.representation layout.tape.wordFits (by have := outputFits layout; omega)
  change descriptionWords (finish layout).code ≤ _ at finished
  have saved := Interactive.retain_descriptionWords_le (Fresh.port layout.tape) (Service.code layout caller zeroValid fuel)
    (Interactive.savedBuffer (Fresh.port layout.tape) (Service.code layout caller zeroValid fuel))
    (Read.tapes layout.tape).representation.encoding.words (Reply.scalarOutput layout.tape).representation.encoding.words
    layout.tape.scalar.representation.encoding.words
  change ((retained layout caller zeroValid fuel).lower (Fresh.port layout.tape)).descriptionWords ≤ _ at saved
  simp only [code, continuation, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  have sizes : (Reply.scalarOutput layout.tape).representation.encoding.words =
    layout.tape.scalar.representation.encoding.words + (Read.tapes layout.tape).representation.encoding.words := rfl
  change _ ≤ 2 * _ + 26 * _ + 78 * (layout.tape.scalar.representation.encoding.words +
    (Read.tapes layout.tape).representation.encoding.words) + 65 * _ + 74
  omega

theorem names (fuel slots : Nat) (localNames : NamesAccounted caller.continuation.code slots)
    (initialNames : NamesAccounted caller.initialCode.code slots) :
    WordIO.NamesAccounted ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape))
      (PrivateSampler.nameBudget layout zeroValid slots) := by
  have body := Service.names layout caller zeroValid fuel slots localNames initialNames
  have saved := Interactive.retain_names (Fresh.port layout.tape) body
    (Read.tapes layout.tape).representation.encoding.words (Reply.scalarOutput layout.tape).representation.encoding.words
    layout.tape.scalar.representation.encoding.words
  exact body.seq ((WordIO.NamesAccounted.compute (Reorder.names _ _ _ _)).seq
    (saved.seq (WordIO.NamesAccounted.compute (Reorder.names _ _ _ _))))

theorem buffers (fuel : Nat) : ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).memBound ≤
    Service.bufferBudget layout caller + 1 := by
  have body := Service.buffers layout caller zeroValid fuel
  have saved := Interactive.retain_buffers (Fresh.port layout.tape) (Service.code layout caller zeroValid fuel)
    (Read.tapes layout.tape).representation.encoding.words (Reply.scalarOutput layout.tape).representation.encoding.words
    layout.tape.scalar.representation.encoding.words
  have prepared := Reorder.buffers (w := w) layout.tape.scalar.representation.encoding.words (Read.tapes layout.tape).representation.encoding.words 0
  have finished := Reorder.buffers (w := w) (Reply.scalarOutput layout.tape).representation.encoding.words layout.tape.scalar.representation.encoding.words 0
  change ((retained layout caller zeroValid fuel).lower (Fresh.port layout.tape)).memBound ≤ _ at saved
  change (prepare layout).code.memBound ≤ 2 at prepared
  change (finish layout).code.memBound ≤ 2 at finished
  change max _ (max (prepare layout).code.memBound (max _ (finish layout).code.memBound)) ≤ _
  unfold Service.bufferBudget at *
  omega

theorem descriptionFits (fuel : Nat)
    (localHeadroom : caller.continuation.code.memBound + 1 < 2 ^ w)
    (initialHeadroom : caller.initialCode.code.memBound + 1 < 2 ^ w) :
    ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).DescriptionFits := by
  have saved := Interactive.retain_descriptionFits (Fresh.port layout.tape) (Service.code layout caller zeroValid fuel)
    (Interactive.savedBuffer (Fresh.port layout.tape) (Service.code layout caller zeroValid fuel))
    (Read.tapes layout.tape).representation.encoding.words (Reply.scalarOutput layout.tape).representation.encoding.words
    layout.tape.scalar.representation.encoding.words layout.tape.wordFits (Service.descriptionFits layout caller zeroValid fuel)
    (Service.savedBuffer_fits layout caller zeroValid fuel localHeadroom initialHeadroom)
    (Read.tapes layout.tape).representation.fits layout.tape.scalar.representation.fits (by have := outputFits layout; omega)
  exact .seq layout.tape.wordFits (Service.descriptionFits layout caller zeroValid fuel)
    (.seq layout.tape.wordFits (.compute (prepare layout).description_fits)
      (.seq layout.tape.wordFits saved (.compute (finish layout).description_fits)))

theorem resources (fuel localTime initialTime slots : Nat)
    (localBound : ∀ value, caller.continuation.time value ≤ localTime)
    (initialBound : ∀ value, caller.initialCode.time value ≤ initialTime)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialCode.code slots)
    (tape : RandomTape w) (saved : Store layout) (valid : ready layout fuel saved)
    (before : State w) (holds : (Read.tapes layout.tape).representation.Holds saved before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout caller zeroValid fuel).execute (Fresh.port layout.tape) .unit tape before)) :
    finished.time ≤ timeBudget layout zeroValid localTime initialTime fuel ∧
    ∃ answer ∈ support (source layout caller zeroValid fuel saved), (output layout).representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)) before
          finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).registerSlots) ∧
          between.SupportBound (max buffers ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).memBound) ∧ between.WellFormed ∧
          (((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).memBound) ≤
              5 * codeBudget layout caller zeroValid fuel + 4 * PrivateSampler.nameBudget layout zeroValid slots +
                registers + 3 * buffers + before.liveMem buffers + timeBudget layout zeroValid localTime initialTime fuel := by
  have words := code_bound layout caller zeroValid fuel
  have named := names layout caller zeroValid fuel slots localNames initialNames
  have reserved : WordIO.NamesBound ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape))
      (PrivateSampler.nameBudget layout zeroValid slots + codeBudget layout caller zeroValid fuel) :=
    ⟨named.registers.trans (Nat.add_le_add_left words _), named.buffers.trans (Nat.add_le_add_left words _)⟩
  have checked := (refines layout caller zeroValid fuel).resources
    (time_bound layout caller zeroValid fuel localTime initialTime localBound initialBound) words reserved
    tape saved valid before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨elapsed, answer, supported, output, execution, visitedBound⟩ := checked
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := visitedBound between visited
  exact ⟨registerBound, bufferBound, wellFormed, by push_cast at memory; omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Pair
