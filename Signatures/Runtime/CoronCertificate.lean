import Signatures.Runtime.CoronMachineReduction
import Signatures.Model.CoCDH
import Signatures.Model.Hardness

/-! A concrete resource certificate for the named Coron co-CDH solver. The source code
and its fixed data are independent of the challenge. Source behavior is required to equal
the original adversary at the actual public key for every challenge, not just one key. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Coron

abbrev challengeInputs : List (Ty CryptoAtom) := [point₁, point₂, point₁, point₂, point₁]

def challengeSetup {Δ : List (Ty CryptoAtom)} :
    Expr CryptoOp (challengeInputs ++ Δ) (.pair point₁ (.pair point₁ point₁)) :=
  .pair (.var .here) (.pair (.var (.there (.there .here)))
    (.var (.there (.there (.there (.there .here))))))

variable {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]

omit [SampleableType F] in
theorem challengeSetup_run (cost : PrimitiveCosts) {Δ : List (Ty CryptoAtom)}
    (data : Env (cryptoBase F G₁ G₂ M M) Δ) (g : G₁) (g₂ : G₂) (X : G₁) (X₂ : G₂) (h : G₁) :
    challengeSetup.run (arithmetic F G₁ G₂ M M cost) (g, g₂, X, X₂, h, data) =
      ⟨(g, X, h), 11⟩ := rfl

/-- Padding the source registers with the five challenge fields avoids an implicit
key-to-environment callback. Exact trace semantics below enforces dependence only on X₂;
the source cannot use the other fields to change its behavior. -/
-- Certify source code, not a runtime assumption about an arbitrary Lean function.
structure SourceCertificate (cost : PrimitiveCosts) (randomBound localTime : Nat)
    -- The three all-path query caps are random calls, hash calls (qH), and signing calls.
    (queries : Fin 3 → Nat) (adv : BLS.CoCDH.Tight.TightAdvPK M G₁ G₂) where
  -- Describe fixed first-order data carried by the source implementation.
  dataTypes : List (Ty CryptoAtom)
  -- These values are fixed independently of the challenge; loading them is charged below.
  data : Env (cryptoBase F G₁ G₂ M M) dataTypes
  -- The executable program returns a message/signature pair and uses bounded-arity randomness.
  code : Program CryptoOp (Command randomBound) (challengeInputs ++ dataTypes) (.pair message point₁)
  -- At every challenge, require exactly the original adversary's oracle computation...
  semantics : ∀ (g : G₁) (g₂ : G₂) (X : G₁) (X₂ : G₂) (h : G₁),
    -- ...under the arithmetic interpreter and source-oracle interpretation...
    code.denote (arithmetic F G₁ G₂ M M cost) (sourceSemantics randomBound)
      -- ...depending behaviorally only on the public key X2.
      (g, g₂, X, X₂, h, data) = adv X₂
  -- Prove source resource bounds at every challenge, not just on average...
  budget : ∀ (g : G₁) (g₂ : G₂) (X : G₁) (X₂ : G₂) (h : G₁),
    -- ...for every adaptive reply path allowed by this oracle contract...
    SourceBudget (arithmetic F G₁ G₂ M M cost) (replies randomBound) kind code
      -- ...with local work <= localTime and per-kind call counts <= queries.
      (g, g₂, X, X₂, h, data) localTime queries

def coCDHWithin (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (budget : Nat) (solver : BLS.CoCDH.CoCDHAdversary F G₁ G₂) : Prop :=
  Machine.Within (F := F) (K := M) (M := M) cost sampling challengeInputs point₁ budget
    (fun env => solver env.1 env.2.1 env.2.2.1 env.2.2.2.1 env.2.2.2.2.1)

variable {cost : PrimitiveCosts} {randomBound localTime : Nat} {queries : Fin 3 → Nat}
  {adv : BLS.CoCDH.Tight.TightAdvPK M G₁ G₂}

def SourceCertificate.package (cert : SourceCertificate (F := F) cost randomBound localTime queries adv)
    (qS : Nat) : Machine.Package (cryptoBase F G₁ G₂ M M) challengeInputs point₁ where
  dataTypes := cert.dataTypes
  data := cert.data
  code := machineReductionCode qS randomBound challengeSetup cert.code

def SourceCertificate.targetBudget
    -- The source certificate contains qH = queries 1 along with the other resource bounds.
    (cert : SourceCertificate (F := F) cost randomBound localTime queries adv)
    -- Sampling prices and the Coron signing limit determine the remaining simulation charges.
    (sampling : Machine.SamplingCosts) (qS : Nat) : Nat :=
  -- Include source local work, all query handlers, cache work, extraction, and public setup.
  machineReductionBound cost sampling qS randomBound localTime 11 queries +
    -- Also charge loading fixed source data and the surrounding machine package.
    (Env.load cert.data).steps + 7

/-- The exact named solver has a general closed-machine implementation within the derived
budget. Only the source implementation is supplied; no finished-solver budget is assumed. -/
theorem SourceCertificate.within
    (cert : SourceCertificate (F := F) cost randomBound localTime queries adv)
    (sampling : Machine.SamplingCosts) (qS : Nat) :
    coCDHWithin (M := M) cost sampling (cert.targetBudget sampling qS)
      (BLS.CoCDH.coronReductionLazyPK (F := F) qS (BLS.CoCDH.Tight.cacheForgeryPK adv)) := by
  refine ⟨cert.package qS, ?_, ?_⟩
  · intro env
    rcases env with ⟨g, g₂, X, X₂, h, ⟨⟩⟩
    rw [Machine.Package.run_eq]
    simp only [Functor.map_map]
    change Run.value <$> (machineReductionCode qS randomBound challengeSetup cert.code).run
        cost sampling (g, g₂, X, X₂, h, cert.data) = _
    rw [machineReductionCode_erase cost sampling g X h qS randomBound challengeSetup cert.code
      (g, g₂, X, X₂, h, cert.data) 11 (challengeSetup_run cost cert.data g g₂ X X₂ h)]
    exact reduction_erase cost (machineSampling sampling qS) g X h g₂ X₂ qS randomBound cert.code
      (g, g₂, X, X₂, h, cert.data) adv (cert.semantics g g₂ X X₂ h)
  · intro env r hr
    rcases env with ⟨g, g₂, X, X₂, h, ⟨⟩⟩
    rw [Machine.Package.run_eq] at hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨z, hz, rfl⟩ := hr
    have hb := machineReductionCode_bound cost sampling g X h qS randomBound challengeSetup cert.code
      (g, g₂, X, X₂, h, cert.data) 11 localTime queries
      (challengeSetup_run cost cert.data g g₂ X X₂ h) (cert.budget g g₂ X X₂ h) z hz
    dsimp [targetBudget, package, challengeInputs] at *
    omega

end Signatures.Runtime.Coron
