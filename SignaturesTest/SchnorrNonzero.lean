import Signatures.Schnorr.Proofs.NonzeroSecurity
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp Schnorr.NonzeroNonce

namespace SignaturesTest.SchnorrNonzero

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

noncomputable local instance : SampleableType (ZMod 5) := SampleableType.ofFintype _
noncomputable local instance : SampleableType (ZMod 5)ˣ := SampleableType.ofFintype _
noncomputable local instance : SampleableType (ZMod 2) := SampleableType.ofFintype _
noncomputable local instance : SampleableType (ZMod 2)ˣ := SampleableType.ofFintype _

-- Zero is repaired; nonzero scalars retain their original value.
example : repair (0 : ZMod 5) (1 : (ZMod 5)ˣ) = 1 := by simp [repair]
example : repair (2 : ZMod 5) (1 : (ZMod 5)ˣ) = 2 := by decide

-- The smallest field is supported: its nonce space contains exactly one value.
example : (sigma (F := ZMod 2) (1 : ZMod 2)).PerfectHVZK (simTranscript 1) := by
  apply sigma_hvzk
  intro x y h
  simpa using h

-- Zero secret keys need no exceptional simulator branch or additional assumption.
example : 𝒮[(sigma (1 : ZMod 5)).realTranscript 0 0] =
    𝒮[simTranscript (F := ZMod 5) 1 0] := by
  apply sigma_hvzk
  · intro x y h; simpa using h
  · simp

-- The collision denominator is four, not five, in this five-element field.
example : (sigma (1 : ZMod 5)).simCommitPredictability
    (simTranscript (F := ZMod 5) 1) ((4 : ENNReal)⁻¹) := by
  simpa using sigma_simCommitPredictability (F := ZMod 5) (1 : ZMod 5)
    (by simp)

-- Verification still accepts a forged identity commitment if its equation holds.
-- Only honest signing nonces are restricted; the verifier is unchanged.
example (x c : ZMod 5) :
    (sigma (F := ZMod 5) (1 : ZMod 5)).verify x 0 c (c * x) = true := by
  simp [sigma, Schnorr.sigma]

end SignaturesTest.SchnorrNonzero

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``Schnorr.NonzeroNonce.signature_sign,
      ``Schnorr.NonzeroNonce.repair_uniform, ``Schnorr.NonzeroNonce.sigma_complete,
      ``Schnorr.NonzeroNonce.sigma_speciallySound, ``Schnorr.NonzeroNonce.sigma_hvzk,
      ``Schnorr.NonzeroNonce.sim_commit, ``Schnorr.NonzeroNonce.sigma_simCommitPredictability,
      ``Schnorr.NonzeroNonce.security] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
