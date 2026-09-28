/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.BLS.CoCDH.Spec.LazyGame
import Signatures.BLS.CoCDH.Spec.Assumption
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# The Coron co-CDH reduction (constructive)

The explicit reduction turning a lazy-ROM BLS forger into a co-CDH solver, with the biased-coin
partitioning that yields the Coron loss `≈ e·qS`.  A persistent per-message coin `k ∈ Fin (qS+1)`
decides whether the co-CDH challenge `h` is embedded into that message's hash: on `k = 0` the hash
is `ρ·g₁ + h` and signing aborts (returns `0`); otherwise the hash is `ρ·g₁` and signing returns
`ρ·X₁`.  A forgery on a `k = 0` message yields `σ* − ρ·X₁ = x·h`.

This module is statement-level: only the reduction definitions (no proofs).
-/

open OracleComp OracleSpec AlgebraicGroupModel BLS.CoCDH.Tight

namespace BLS.CoCDH

section Coin

variable {D R : Type} [DecidableEq D] [Finite D] [Finite R] [Nonempty R]
  [SampleableType R] [SampleableType (D → R)]

/-- Interpret ordinary uniform queries honestly and coin queries with a lazy sample-and-cache
random oracle. -/
noncomputable def lazyCoinImpl :
    QueryImpl (unifSpec + (D →ₒ R))
      (StateT (D →ₒ R).QueryCache ProbComp) :=
  unifFwdImpl (D →ₒ R) + (randomOracle (spec := (D →ₒ R)))

end Coin

section Reduction

variable {F M G₁ G₂ : Type} [Field F] [SampleableType F]
  [Fintype M] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂]

/-- Coron oracle whose persistent coin is obtained from the ambient `M →ₒ Fin (qS + 1)` oracle:
`k = 0` embeds the challenge `h` in the hash and aborts signing; otherwise honest. -/
noncomputable def coronOracleLazy (g₁ X₁ h : G₁) (qS : ℕ) :
    QueryImpl (advSpec M G₁)
      (StateT ((M → Option F) × Finset M)
        (OracleComp (unifSpec + (M →ₒ Fin (qS + 1))))) :=
  fun q => match q with
    | Sum.inl (Sum.inl n) =>
        (liftM (liftM ((unifSpec + (M →ₒ Fin (qS + 1))).query (Sum.inl n)) :
          OracleComp (unifSpec + (M →ₒ Fin (qS + 1))) (Fin (n + 1))) :
          StateT ((M → Option F) × Finset M)
            (OracleComp (unifSpec + (M →ₒ Fin (qS + 1)))) (Fin (n + 1)))
    | Sum.inl (Sum.inr m) => do
        let ρ ← (liftM (getDlogS (F := F) m) :
          StateT ((M → Option F) × Finset M)
            (OracleComp (unifSpec + (M →ₒ Fin (qS + 1)))) F)
        let k ← (liftM (liftM ((M →ₒ Fin (qS + 1)).query m) :
          OracleComp (unifSpec + (M →ₒ Fin (qS + 1))) (Fin (qS + 1))) :
          StateT ((M → Option F) × Finset M)
            (OracleComp (unifSpec + (M →ₒ Fin (qS + 1)))) (Fin (qS + 1)))
        pure (ρ • g₁ + (if k = 0 then h else 0))
    | Sum.inr m => do
        modify (fun s => (s.1, insert m s.2))
        let ρ ← (liftM (getDlogS (F := F) m) :
          StateT ((M → Option F) × Finset M)
            (OracleComp (unifSpec + (M →ₒ Fin (qS + 1)))) F)
        let k ← (liftM (liftM ((M →ₒ Fin (qS + 1)).query m) :
          OracleComp (unifSpec + (M →ₒ Fin (qS + 1))) (Fin (qS + 1))) :
          StateT ((M → Option F) × Finset M)
            (OracleComp (unifSpec + (M →ₒ Fin (qS + 1)))) (Fin (qS + 1)))
        pure (if k = 0 then (0 : G₁) else ρ • X₁)

/-- The computation inside the lazy reduction, before interpreting its persistent coin oracle. -/
noncomputable def coronReductionProgram (g₁ X₁ : G₁) (X₂ : G₂) (h : G₁) (qS : ℕ)
    (adv : TightAdvPK M G₁ G₂) :
    OracleComp (unifSpec + (M →ₒ Fin (qS + 1))) G₁ := do
  let ((mstar, σstar), st) ←
    (simulateQ (coronOracleLazy (F := F) g₁ X₁ h qS) (adv X₂)).run
      ((fun _ => none), ∅)
  pure (σstar - ((st.1 mstar).getD 0) • X₁)

/-- **The Coron co-CDH reduction** from a lazy-ROM BLS forger, with lazy per-message coins. -/
noncomputable def coronReductionLazyPK (qS : ℕ) (adv : TightAdvPK M G₁ G₂) :
    CoCDHAdversary F G₁ G₂ :=
  fun g₁ _g₂ X₁ X₂ h =>
    (simulateQ (lazyCoinImpl (D := M) (R := Fin (qS + 1)))
      (coronReductionProgram (F := F) g₁ X₁ X₂ h qS adv)).run' ∅

end Reduction

end BLS.CoCDH
