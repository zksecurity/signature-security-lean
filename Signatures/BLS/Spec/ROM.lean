/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.BLS.Spec.ROMInterface

/-!
# The ordinary BLS random-oracle handler

The private state records sampled hash exponents and messages submitted for signing.
Hashing, signing, and final verification share this state. With `X₁ = secret • g₁`,
the signing reply `ρ • X₁` is exactly `secret • H(message)`.
-/

open OracleComp OracleSpec

namespace BLS.ROM

/-- Private state shared by hashing, signing, and verification. -/
structure State (F M : Type) where
  hashExponents : M → Option F
  signedMessages : Finset M

/-- Initially, no message has been hashed or signed. -/
def State.empty {F M : Type} : State F M :=
  { hashExponents := fun _ => none, signedMessages := ∅ }

/-- A probabilistic computation carrying the private oracle state. -/
abbrev OracleM (F M : Type) := StateT (State F M) ProbComp

variable {F M G₁ : Type} [SampleableType F] [DecidableEq M] [SMul F G₁]

/-- Reuse a message's hash exponent, or sample and remember it on first use. -/
noncomputable def hashScalar (message : M) : OracleM F M F := do
  match (← get).hashExponents message with
  | some scalar => return scalar
  | none =>
      let scalar ← ($ᵗ F : ProbComp F)
      modify fun state =>
        { state with hashExponents := Function.update state.hashExponents message (some scalar) }
      return scalar

/-- Answer ordinary BLS requests; `X₁` is the secret-key multiple of `g₁`. -/
noncomputable def oracle (g₁ X₁ : G₁) : QueryImpl (advSpec M G₁) (OracleM F M)
  | Request.random n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | Request.hash message => do
      let scalar ← hashScalar (F := F) message
      return scalar • g₁
  | Request.sign message => do
      modify fun state => { state with signedMessages := insert message state.signedMessages }
      let scalar ← hashScalar (F := F) message
      return scalar • X₁

end BLS.ROM
