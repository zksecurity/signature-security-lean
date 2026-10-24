import Proofs.Runtime.Caliper.SchnorrROMReplayExtractFull
import Proofs.Runtime.Caliper.SchnorrROMReplayExtractCodeBounds

/-! Resources of the complete executed solver: the initialized fork controller's
derived account followed by the extractor's locally derived account. Nothing is
assumed about a completed-controller budget beyond the controller's own
verified bounds. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Zero F] [SMul F G] [Sub G]
    [DecidableEq M] [DecidableEq G] [DecidableEq F] [Sub F] [Div F]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Pass.Caller config A)
    (ops : Handler.Operations config) (qH : Nat) (indexFits : qH + 1 < 2 ^ w)
    (budget : Handler.Budget config ops)
    (localBudget : SchnorrROM.Caller.LocalBudget config (caller.routines config))
    (arith : Arithmetic config) (arithBudget : Arithmetic.Budget config arith)

/-- Time budget of the full solver. -/
def fullTimeBudget (fuel : Nat) : Nat :=
  Initialized.timeBudget config caller ops qH indexFits budget localBudget fuel + timeBudget config arith arithBudget
/-- Stored-code budget of the full solver. -/
def fullCodeBudget (fuel : Nat) : Nat :=
  Initialized.codeBudget config caller ops qH indexFits budget localBudget fuel + codeBudget config arith arithBudget + 1
/-- Name budget of the full solver. -/
def fullNameBudget (slots : Nat) : Nat := max (ReplayFork.nameBudget config ops slots) (nameBudget config arith)
/-- Buffer-name extent of the full solver. -/
def fullBufferBudget : Nat := max (Pass.bufferBudget config caller ops + 1) (bufferBudget config arith)

theorem full_time (fuel : Nat) (tables : fuel + 1 ≤ config.capacityPred + 1)
    (tapes : 6 * fuel + 3 ≤ config.sampler.capacity) :
    Interactive.TimeBound (Fresh.port config.handler.sampler.tape) .unit (Setup.input config)
      (fullProgram config caller ops qH indexFits arith fuel)
      (fullTimeBudget config caller ops qH indexFits budget localBudget arith arithBudget fuel) :=
  Interactive.TimeBound.seq (Initialized.refines config caller ops qH indexFits fuel tables tapes)
    (Initialized.time config caller ops qH indexFits budget localBudget fuel tables tapes)
    (time config arith arithBudget)

theorem full_words (fuel : Nat) :
    ((fullProgram config caller ops qH indexFits arith fuel).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
      fullCodeBudget config caller ops qH indexFits budget localBudget arith arithBudget fuel := by
  have controller := Initialized.words config caller ops qH indexFits budget localBudget fuel
  have extractor := words config arith arithBudget
  change (WordIO.Code.seq ((Initialized.program config caller ops qH indexFits fuel).lower _)
    ((code config arith).lower _)).descriptionWords ≤ _
  rw [WordIO.Code.descriptionWords_seq]
  unfold fullCodeBudget
  omega

theorem full_names (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots)
    (initialNames : NamesAccounted caller.initialization.code slots) (fuel : Nat) :
    WordIO.NamesAccounted ((fullProgram config caller ops qH indexFits arith fuel).lower (Fresh.port config.handler.sampler.tape))
      (fullNameBudget config ops arith slots) :=
  ((Initialized.names config caller ops qH indexFits slots handlerRoom localNames initialNames fuel).mono
    (le_max_left _ _)).seq ((names config arith).mono (le_max_right _ _))

theorem full_buffers (fuel : Nat) :
    ((fullProgram config caller ops qH indexFits arith fuel).lower (Fresh.port config.handler.sampler.tape)).memBound ≤
      fullBufferBudget config caller ops arith :=
  max_le ((Initialized.buffers config caller ops qH indexFits fuel).trans (le_max_left _ _))
    ((buffers config arith).trans (le_max_right _ _))

theorem full_descriptionFits (room : Pass.replayNameRoom config caller ops) (fuel : Nat) :
    ((fullProgram config caller ops qH indexFits arith fuel).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  .seq config.sampler.wordFits (Initialized.descriptionFits config caller ops qH indexFits room fuel)
    (descriptionFits config arith)

/-- Every execution of the full solver stays within the derived time budget,
returns a represented answer of the full source, and every visited state obeys
the register, buffer and total-memory bounds. -/
theorem full_resources (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots)
    (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) (tables : fuel + 1 ≤ config.capacityPred + 1)
    (tapes : 6 * fuel + 3 ≤ config.sampler.capacity)
    (tape : RandomTape w) (value : (Pass.Initialization.points config).Value)
    (before : State w) (holds : (Setup.input config).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers)
    (initialBuffers : before.SupportBound buffers) (finished : WordIO.Result w)
    (reached : some finished ∈ support ((fullProgram config caller ops qH indexFits arith fuel).execute
      (Fresh.port config.handler.sampler.tape) .unit tape before)) :
    let lowered := (fullProgram config caller ops qH indexFits arith fuel).lower (Fresh.port config.handler.sampler.tape)
    let stored := fullCodeBudget config caller ops qH indexFits budget localBudget arith arithBudget fuel
    let elapsed := fullTimeBudget config caller ops qH indexFits budget localBudget arith arithBudget fuel
    finished.time ≤ elapsed ∧ ∃ answer ∈ support (fullSource config caller ops qH indexFits fuel tables tapes value),
      config.handler.sampler.tape.scalar.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape lowered before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers lowered.registerSlots) ∧ between.SupportBound (max buffers lowered.memBound) ∧
          between.WellFormed ∧
          (lowered.staticWords registers buffers : Int) + between.liveMem (max buffers lowered.memBound) ≤
            stored + 4 * (fullNameBudget config ops arith slots + stored) + registers + 3 * buffers +
              before.liveMem buffers + elapsed := by
  have stored := full_words config caller ops qH indexFits budget localBudget arith arithBudget fuel
  have named := full_names config caller ops qH indexFits arith slots handlerRoom localNames initialNames fuel
  exact (full_refines config caller ops qH indexFits arith fuel tables tapes).resources
    (full_time config caller ops qH indexFits budget localBudget arith arithBudget fuel tables tapes) stored
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
    tape value before holds registers buffers initialRegisters initialBuffers finished reached

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
