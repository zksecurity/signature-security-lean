/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-! The ordinary BLS query interface. Named request patterns expose the three
operations while retaining the oracle-library encoding used by the reductions. -/

open OracleComp OracleSpec

namespace BLS.ROM

abbrev advSpec (M G₁ : Type) := (unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)

abbrev Request (M : Type) := (advSpec M Unit).Domain

namespace Request

@[match_pattern] abbrev random {M : Type} (n : Nat) : Request M := .inl (.inl n)
@[match_pattern] abbrev hash {M : Type} (message : M) : Request M := .inl (.inr message)
@[match_pattern] abbrev sign {M : Type} (message : M) : Request M := .inr message

end Request

/-- An arbitrary oracle computation returning a message and candidate signature. -/
abbrev Adversary (M G₁ : Type) := OracleComp (advSpec M G₁) (M × G₁)

/-- The attacker receives the verification key before making adaptive requests. -/
abbrev AdversaryPK (M G₁ G₂ : Type) := G₂ → Adversary M G₁

/-- Request a hash through the attacker's oracle interface. -/
abbrev hash {M G₁ : Type} (message : M) : OracleComp (advSpec M G₁) G₁ :=
  liftM ((advSpec M G₁).query (Request.hash message))


end BLS.ROM
