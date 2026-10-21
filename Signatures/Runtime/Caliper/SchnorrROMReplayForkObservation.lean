import Signatures.Runtime.Caliper.SchnorrROMReplayForkExpansion

/-! Observe successful terminal frames as the original list-cache pass outputs.
Tape metadata remains available to the controller until after both passes. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} (config : Signing.Enumerated.Configuration w M F G)

abbrev OriginalPass := ((M × G × F) × F) × Schnorr.ListROM.Shared.Caches F G M
def observedPass (value : Terminal.Output config) : Option (OriginalPass (M := M) (F := F) (G := G)) :=
  (Pass.observed config value).1
def observed (value : Result config) : Option (OriginalPass (M := M) (F := F) (G := G) × OriginalPass (M := M) (F := F) (G := G)) :=
  match value with
  | .inl _ => none
  | .inr pair => (observedPass config pair.1).bind fun first => (observedPass config pair.2).map fun second => (first, second)
def publicPoints (value : Terminal.Output config) : (Pass.Initialization.points config).Value :=
  ⟨value.2.val.1.1, value.2.property.1.1⟩

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G]

noncomputable def originalSelection (qH : Nat) (value : Option (OriginalPass (M := M) (F := F) (G := G))) :=
  value.bind (Schnorr.selectPass (G₂ := G) (K := M) PrimitiveCosts.unit qH)
theorem selection_original (qH : Nat) (value : Terminal.Output config) :
    Schnorr.asIndex qH (PassSelection.source config qH value) = originalSelection qH (observedPass config value) := by
  rw [PassSelection.source_original config PrimitiveCosts.unit qH value]
  cases returned : (Terminal.observed config value).1 <;>
    simp [originalSelection, observedPass, Pass.observed, returned]

variable (caller : Pass.Caller config A) (ops : Handler.Operations config)
    (fuel : Nat) (witness : Pass.Caller.Source config caller fuel)

def originalMain (points : (Pass.Initialization.points config).Value) :=
  letI := PrivateSampler.Enumerated.sampleable config.sampler
  (Schnorr.ListROM.pass (G₂ := G) (K := M)
    (Subtype.val <$> witness.program (witness.inputView ⟨points.val.2, points.property.2⟩))).run (points.val, [], [])

theorem pass_original (value : Pass.Initialization.Input config) (room : Pass.Initialization.admitted config fuel value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    Pass.observed config <$> Pass.source config caller ops fuel value =
      (fun result => (some result.1, result.2)) <$>
        Schnorr.ListROM.Shared.tapeRun (originalMain config caller fuel witness value.2) value.1.val :=
  Pass.source_tapeRun (G₂ := G) (K := M) config caller ops fuel witness value room

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
