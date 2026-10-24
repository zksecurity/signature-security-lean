import Proofs.Runtime.Caliper.SchnorrROMReplayChallenge

/-! Charge the fresh oracle call, retained slot/first result, and repacking.
The resource theorem follows the same execution through every visited state. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayChallenge
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

def timeBudget := 34 + 12 * (input config).encoding.words + 8 * (ReplaySecond.rawInput config).encoding.words
def codeBudget := 39 * (input config).encoding.words + 26 * (ReplaySecond.rawInput config).encoding.words + 208

theorem held_time : Interactive.TimeBound (Fresh.port config.handler.sampler.tape) .unit
    (input config) (heldCode config) (34 + 12 * (input config).encoding.words) := by
  have kept := (PrivateSampler.Enumerated.Direct.time_bound config.sampler).retain
    (PrivateSampler.Enumerated.Direct.refines config.sampler) (by decide) (input config) config.sampler.wordFits (heldInput config).fits
  have viewed := kept.viewInput (input config) (fun value => (⟨(), trivial⟩, value)) (fun _ => rfl)
  exact viewed.mono (Interactive.retain_time_unit_le _ 0 1 _ 26)

theorem time : Interactive.TimeBound (Fresh.port config.handler.sampler.tape) .unit
    (input config) (program config) (timeBudget config) :=
  Interactive.TimeBound.seq (held_refines config) (held_time config)
    (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
      (repack config) _ (ByteRoute.time _ _ _ _ _ _ _ _))

theorem words : ((program config).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ codeBudget config := by
  have kept := Interactive.retain_descriptionWords_le (Fresh.port config.handler.sampler.tape)
    (PrivateSampler.Enumerated.Direct.code config.sampler)
      (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape) (PrivateSampler.Enumerated.Direct.code config.sampler))
        0 1 (input config).encoding.words
  have drawn := PrivateSampler.Enumerated.Direct.code_words config.sampler
  change ((PrivateSampler.Enumerated.Direct.code config.sampler).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ 125 at drawn
  have repacked : descriptionWords (repack config).code ≤ 26 * (ReplaySecond.rawInput config).encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
  change ((heldCode config).lower _).descriptionWords ≤ _ at kept
  change (WordIO.Code.seq ((heldCode config).lower _) (.compute (repack config).code)).descriptionWords ≤ _
  rw [WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names : WordIO.NamesAccounted ((program config).lower (Fresh.port config.handler.sampler.tape)) 3 :=
  (Interactive.retain_names (Fresh.port config.handler.sampler.tape)
    (PrivateSampler.Enumerated.Direct.names config.sampler).accounted 0 1 (input config).encoding.words).seq
      (WordIO.NamesAccounted.compute (ByteRoute.names _ _ _ _ _ _ _ _ 3))

theorem buffers : ((program config).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 3 := by
  have kept := Interactive.retain_buffers (Fresh.port config.handler.sampler.tape)
    (PrivateSampler.Enumerated.Direct.code config.sampler) 0 1 (input config).encoding.words
  have drawn := PrivateSampler.Enumerated.Direct.buffers config.sampler
  change ((PrivateSampler.Enumerated.Direct.code config.sampler).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 2 at drawn
  have repacked : (repack config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
  change ((heldCode config).lower _).memBound ≤ _ at kept
  change max ((heldCode config).lower _).memBound (repack config).code.memBound ≤ _
  omega

theorem savedNameFits : Interactive.savedBuffer (Fresh.port config.handler.sampler.tape)
    (PrivateSampler.Enumerated.Direct.code config.sampler) < 2 ^ w := by
  have drawn := PrivateSampler.Enumerated.Direct.buffers config.sampler
  change ((PrivateSampler.Enumerated.Direct.code config.sampler).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 2 at drawn
  have room := config.sampler.wordFits
  unfold Interactive.savedBuffer
  omega

theorem descriptionFits : ((program config).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  .seq config.sampler.wordFits
    (Interactive.retain_descriptionFits (Fresh.port config.handler.sampler.tape) (PrivateSampler.Enumerated.Direct.code config.sampler)
      _ 0 1 (input config).encoding.words config.sampler.wordFits (PrivateSampler.Enumerated.Direct.descriptionFits config.sampler)
        (savedNameFits config) (by have := config.sampler.wordFits; omega) (input config).fits (heldOutput config).fits)
    (.compute (repack config).description_fits)

theorem resources (tape : RandomTape w) (value : Input config) (before : State w) (holds : (input config).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program config).execute (Fresh.port config.handler.sampler.tape) .unit tape before)) :
    let code := (program config).lower (Fresh.port config.handler.sampler.tape)
    finished.time ≤ timeBudget config ∧ ∃ answer ∈ support (source config value),
      (ReplaySecond.rawInput config).Holds answer finished.state ∧ answer.2 = value.2 ∧ answer.1.1 = value.1 ∧
      ∃ execution : WordIO.Exec .unit tape code before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers code.registerSlots) ∧ between.SupportBound (max buffers code.memBound) ∧ between.WellFormed ∧
          (code.staticWords registers buffers : Int) + between.liveMem (max buffers code.memBound) ≤
            codeBudget config + 4 * (3 + codeBudget config) + registers + 3 * buffers + before.liveMem buffers + timeBudget config := by
  have stored := words config
  have named := names config
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    (refines config).resources (time config) stored
      ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
      tape value before holds registers buffers initialRegisters initialBuffers finished reached
  have retained := retains_first config value answer supported
  exact ⟨elapsed, answer, supported, represented, retained.1, retained.2, execution, memory⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayChallenge
