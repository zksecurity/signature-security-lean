import Proofs.Runtime.Caliper.SchnorrROMReplayMatchSource

/-! The executed second branch: restart the tapes, run the adversary again,
select its fork point and compare it with the retained first-pass slot. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplaySecond.Selected
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Pass.Caller config A) (ops : Handler.Operations config)
    (qH : Nat) (indexFits : qH + 1 < 2 ^ w)

def program (fuel : Nat) : Interactive.Code w :=
  .seq (ReplaySecond.program config caller ops fuel) (.compute (ReplayMatch.realizer config ops qH indexFits).code)
def source (fuel : Nat) (value : {value : Request config // ready config fuel value}) :=
  ReplayMatch.source config qH <$> ReplaySecond.source config caller ops fuel value

theorem refines (fuel : Nat) : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit
    (input config fuel) (ReplayMatch.output config) (source config caller ops qH fuel) (program config caller ops qH indexFits fuel) := by
  unfold Selected.source Selected.program
  simpa only [bind_pure_comp] using (ReplaySecond.refines config caller ops fuel).seq
    (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (ReplayMatch.realizer config ops qH indexFits))

theorem retained_first (fuel : Nat) (value : {value : Request config // ready config fuel value})
    (answer) (reached : answer ∈ support (source config caller ops qH fuel value)) : answer.2.2 = value.val := by
  simp only [Selected.source, support_map, Set.mem_image] at reached
  obtain ⟨second, reached, rfl⟩ := reached
  exact ReplaySecond.retained_first config caller ops fuel value second reached

theorem buffers (fuel : Nat) : ((program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).memBound ≤
    Pass.bufferBudget config caller ops + 1 := by
  have second := ReplaySecond.buffers config caller ops fuel
  have matching := ReplayMatch.buffers config ops qH indexFits
  change max ((ReplaySecond.program config caller ops fuel).lower _).memBound
    (ReplayMatch.realizer config ops qH indexFits).code.memBound ≤ _
  unfold Pass.bufferBudget at *
  omega

theorem descriptionFits (room : Pass.replayNameRoom config caller ops) (fuel : Nat) :
    ((program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  .seq config.sampler.wordFits (ReplaySecond.descriptionFits config caller ops room fuel)
    (.compute (ReplayMatch.realizer config ops qH indexFits).description_fits)

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplaySecond.Selected
