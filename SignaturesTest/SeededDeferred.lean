import Signatures.Runtime.SeededDeferredTrace
import Signatures.Runtime.SeededSuffixSampling
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
import Lean.Util.CollectAxioms

/-! Deferred sampling must preserve unused entries jointly with an adaptive
first path, including entries first visited during replay. -/

open OracleComp OracleSpec MeasureTheory Signatures.Runtime
open Signatures.Runtime.SeededDeferred Signatures.Runtime.SeededTrace

namespace SignaturesTest.SeededDeferred

local instance : unifSpec ⊂ₒ unifSpec where
  monadLift := id
  onQuery := id
  onResponse _ := id
  liftM_eq_lift q := by cases q; rfl

local instance : unifSpec ˡ⊂ₒ unifSpec where
  onResponse_bijective _ := Function.bijective_id

private def budget (i : Nat) : Nat := if i = 1 then 2 else if i = 2 then 1 else 0

private theorem cover : SeedListCovers budget [1, 2] := by
  intro i hi
  by_cases h₁ : i = 1
  · simp [h₁]
  · by_cases h₂ : i = 2
    · simp [h₂]
    · simp [budget, h₁, h₂] at hi

private def adaptive : ProbComp (Fin 2 × Nat) := do
  let bit ← unifSpec.query 1
  if bit = 0 then
    let other ← unifSpec.query 1
    pure (bit, other.val)
  else
    let other ← unifSpec.query 2
    pure (bit, other.val)

private theorem adaptive_bound : IsPerIndexQueryBound adaptive budget := by
  simp only [adaptive, isPerIndexQueryBound_query_bind_iff]
  constructor
  · decide
  · intro bit
    by_cases h : bit = 0 <;> simp [h, IsPerIndexQueryBound, budget, Function.update]

/-- The result observes both the first bit and an unused value from that same
family. Deferral must preserve their correlation across the branch. -/
example :
    𝒟[do
      let seed ← generateSeed unifSpec budget [1, 2]
      let result ← (simulateQ seededOracle adaptive).run seed
      pure (result.1.1, (result.2 1)[0]?)] =
    𝒟[do
      let result ← (simulateQ budgetOracle adaptive).run budget
      let rest ← generateSeed unifSpec result.2 [1, 2]
      pure (result.1.1, (rest 1)[0]?)] := by
  simpa only [liftComp_self] using defer adaptive budget adaptive_bound [1, 2]
    (by decide) cover (fun result rest => pure (result.1, (rest 1)[0]?))

/-- Complete reconstruction keeps an unused private entry after the recorded
entry, and keeps a family that was never requested in the first execution. -/
private def suffix : QuerySeed unifSpec := fun i =>
  if h : i = 1 then h.symm ▸ [(0 : Fin 2)]
  else if h : i = 2 then h.symm ▸ [(2 : Fin 3)] else []

example : restore [⟨1, (1 : Fin 2)⟩] suffix 1 = [1, 0] := rfl
example : restore [⟨1, (1 : Fin 2)⟩] suffix 2 = [2] := rfl

/-- Deleting the selected family's unused entries must still preserve a
different family's unseen value distribution when replay first visits it. -/
example :
    𝒟[do
      let seed ← generateSeed unifSpec budget [1, 2]
      (simulateQ seededOracle (unifSpec.query 2 : ProbComp (Fin 3))).run'
        (append ∅ (seed.update 1 []))] =
      𝒟[(simulateQ seededOracle (unifSpec.query 2 : ProbComp (Fin 3))).run' ∅] := by
  simpa only [liftComp_self] using generate_erased_suffix_run
    (unifSpec.query 2 : ProbComp (Fin 3)) budget [1, 2] ∅ 1

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``generate_bind_step, ``query_bind_step, ``defer,
      ``budget_run'_eq, ``restore_run, ``defer_original_seed, ``restore_eq_append,
      ``reset_append, ``generate_suffix_run, ``generate_erased_suffix_run,
      ``generate_reset_run] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``defer, ``defer_original_seed, ``generate_reset_run] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      unless conclusion.isAppOf ``Eq do
        throwError "{name}: must preserve a complete distribution"
      if (conclusion.find? (fun e => e.isConstOf ``instEvalDistSemanticsOfMonadLiftTSPMF)).isSome then
        throwError "{name}: statement must use the native measure interpretation"
      for param in params do
        let declaration ← getFVarLocalDecl param
        if declaration.userName == `I then
          for premise in params do
            let type ← inferType premise
            if (type.isAppOf ``Finite || type.isAppOf ``Fintype) &&
                (type.find? (fun e => e == param)).isSome then
              throwError "{name}: must not require a finite oracle-family universe"

end SignaturesTest.SeededDeferred
