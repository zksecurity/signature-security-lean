/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Defs

/-!
# Token-indexed outputs for the signature adapter

These utilities retain the signature game's grouped coefficient format and interpret it over
the generator and received replies. They are independent of the generic interactive AGM API.
-/

namespace AlgebraicGroupModel

/-- The finite group inputs made available by a game, labeled by its choice of tokens. -/
abbrev Transcript (Token G : Type) := List (Token × G)

/-- Coefficients on input tokens; only tokens in the supplied transcript are evaluated. -/
abbrev Representation (F Token : Type) := Token → F

/-- Evaluate an algebraic representation using only the inputs supplied by the game. -/
def Representation.eval {F Token G : Type} [AddMonoid G] [SMul F G]
    (coeff : Representation F Token) (inputs : Transcript Token G) : G :=
  (inputs.map fun p => coeff p.1 • p.2).sum

/-- An algebraic group output together with an arbitrary non-group payload. -/
structure Output (F Token Payload : Type) where
  value : Payload
  coefficients : Representation F Token

/-- Materialize the group output while preserving its accompanying payload. -/
def Output.materialize {F Token Payload G : Type} [AddMonoid G] [SMul F G]
    (out : Output F Token Payload) (inputs : Transcript Token G) : Payload × G :=
  (out.value, out.coefficients.eval inputs)

/-- Separate input blocks can be evaluated independently, in their original order. -/
theorem Representation.eval_append {F Token G : Type} [AddMonoid G] [SMul F G]
    (coeff : Representation F Token) (xs ys : Transcript Token G) :
    coeff.eval (xs ++ ys) = coeff.eval xs + coeff.eval ys := by
  simp [eval, List.sum_append]

end AlgebraicGroupModel
