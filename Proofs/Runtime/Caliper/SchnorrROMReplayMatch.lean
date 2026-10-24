import Proofs.Runtime.Caliper.SchnorrROMReplayMatchCheck

/-! Execute the second forgery's selector and its comparison with the retained
fork slot. Both pass results survive selection and comparison unchanged. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayMatch
open Caliper BoundedSource
variable {w : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (ops : Handler.Operations config)
    (qH : Nat) (indexFits : qH + 1 < 2 ^ w)

theorem selectionNameFits : (PassSelection.realizer config ops qH indexFits).savedBuffer < 2 ^ w := by
  have bounded := PassSelection.buffers config ops qH indexFits
  have reserve := ops.reserve
  have width := config.sampler.wordFits
  unfold Realizer.savedBuffer
  omega
def selection := (PassSelection.realizer config ops qH indexFits).retain (by decide) (frame config)
  config.sampler.wordFits (selectionNameFits config ops qH indexFits) (prepared config).fits (selected config).fits
def selectionValue (value : Frame config) : (Selection.result config).Value × Frame config :=
  (⟨PassSelection.source config qH value.1, PassSelection.valid config ops qH indexFits value.1⟩, value)
def source (qH : Nat) (value : Frame config) : (Selection.boolean config).Value × Frame config :=
  (⟨Check.source (PassSelection.source config qH value.1, value.2.1.1.val), trivial⟩, value)
def realizer : Realizer .unit (frame config) (output config) (source config qH) :=
  ((((prepare config).then (selection config ops qH indexFits)).then (arguments config)).then (Check.retained config)).viewOutput
    (output config) (source config qH) (fun _ => rfl)
def implementation : Implementation .unit (Layout.all (frame config)) (Layout.all (output config)) (source config qH) where
  preserves _ _ := trivial
  program := ((realizer config ops qH indexFits).viewInput (Layout.all (frame config)).representation Subtype.val (fun _ => rfl)).viewOutput
    (Layout.all (output config)).representation (fun value => ⟨source config qH value.val, trivial⟩) (fun _ => rfl)

omit [Zero F] in
theorem preserves_frame (value : Frame config) : (source config qH value).2 = value := rfl
theorem names : NamesAccounted (realizer config ops qH indexFits).code (max 3 ops.slots) :=
  (((ByteRoute.names _ _ _ _ _ _ _ _ _).seq
    (Retain.names (PassSelection.names config ops qH indexFits) _ _ _)).seq
      (ByteRoute.names _ _ _ _ _ _ _ _ _)).seq
        (Retain.names ((Check.constructed config).names _) _ _ _)
theorem buffers : (realizer config ops qH indexFits).code.memBound ≤ max 8 (ops.slots + 3) + 1 := by
  have preparedBound : (prepare config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
  have selected := (PassSelection.realizer config ops qH indexFits).retain_buffers (by decide) (frame config)
    config.sampler.wordFits (selectionNameFits config ops qH indexFits) (prepared config).fits (selected config).fits
  have selector := PassSelection.buffers config ops qH indexFits
  have arguments : (arguments config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
  have checked := (Check.constructed config).implementation.program.retain_buffers (by decide) (frame config)
    config.sampler.wordFits (Check.nameFits config) (checking config).fits (output config).fits
  have checker := (Check.constructed config).buffers_le
  rw [Check.buffers] at checker
  change (selection config ops qH indexFits).code.memBound ≤ _ at selected
  change (Check.retained config).code.memBound ≤ _ at checked
  change max (max (max (prepare config).code.memBound (selection config ops qH indexFits).code.memBound)
    (ReplayMatch.arguments config).code.memBound) (Check.retained config).code.memBound ≤ _
  omega

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayMatch
