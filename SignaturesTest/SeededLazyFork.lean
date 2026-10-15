import Signatures.Runtime.SeededForkReachability
import Signatures.Runtime.SchnorrLazyFork
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
import Lean.Util.CollectAxioms

/-! The complete fork must preserve joint adaptive outputs, guard against an
unchanged challenge, and allow previously unseen replay families. -/

open OracleComp OracleSpec MeasureTheory Signatures.Runtime
open Signatures.Runtime.SeededDeferred Signatures.Runtime.SeededLazyFork

namespace SignaturesTest.SeededLazyFork

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

private theorem adaptive_slot (result : (Fin 2 × Nat) × QueryLog unifSpec)
    (supported : result ∈ support adaptive.withQueryLog) :
    0 < (SeededTrace.restore result.2 ∅ 1).length := by
  change result ∈ support ((OracleComp.queryBind 1 fun bit : Fin 2 =>
    if bit = 0 then
      (unifSpec.query 1 : ProbComp (Fin 2)) >>= fun other => pure (bit, other.val)
    else
      (unifSpec.query 2 : ProbComp (Fin 3)) >>= fun other => pure (bit, other.val)).withQueryLog) at supported
  rw [Replay.withQueryLog_queryBind, OracleComp.queryBind,
    PFunctor.FreeM.mem_support_liftBind] at supported
  obtain ⟨bit, supported⟩ := supported
  rw [support_map] at supported
  obtain ⟨rest, _, rfl⟩ := supported
  simp [SeededTrace.restore]

/-- A successful changed-bit replay switches branches: a Fin3 family can be
first encountered on the second run. The equality observes both full outputs. -/
example :
    𝒟[seededFork adaptive budget [1, 2] 1 (fun _ => some 0)] =
      𝒟[recordedFork adaptive 1 (fun _ => some (0 : Fin (budget 1 + 1)))] := by
  apply seededFork_eq_recordedFork adaptive budget adaptive_bound [1, 2]
    (by decide) cover 1 (fun _ => some 0)
  intro result supported slot selected
  have hslot : slot = 0 := (Option.some.inj selected).symm
  subst slot
  exact adaptive_slot result supported

/-- The old-value guard still rejects a same-answer replacement before any
second execution. -/
private def recorded : QuerySeed unifSpec :=
  SeededTrace.restore [⟨1, (1 : Fin 2)⟩] ∅

example : afterFirst (pure () : ProbComp Unit) 1 (fun _ => some (0 : Fin 1)) () recorded = (do
    let fresh ← ($ᵗ Fin 2 : ProbComp (Fin 2))
    if fresh = 1 then pure none else pure (some ((), ()))) := by
  simp [afterFirst, recorded, SeededTrace.restore, liftComp_self, eq_comm]

/-- The finite-list codec preserves every family in chronological order. -/
example : Schnorr.SeedTape.toSeed (Schnorr.encodeTape
      ([⟨.inr (), (1 : Fin 2)⟩, ⟨.inl (.inl 1), (0 : Fin 2)⟩,
        ⟨.inl (.inr ()), (0 : Fin 2)⟩] : QueryLog (Schnorr.replaySpec (Fin 2)))) =
    SeededTrace.restore [⟨.inr (), (1 : Fin 2)⟩, ⟨.inl (.inl 1), (0 : Fin 2)⟩,
      ⟨.inl (.inr ()), (0 : Fin 2)⟩] ∅ :=
  Schnorr.LazySeed.toSeed_encode _

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``budget_result_supported, ``logged_run_erase, ``defer_continuation,
      ``defer_reset_run, ``restore_entry, ``afterFirst_suffix,
      ``seededFork_eq_recordedFork, ``within_of_reachable,
      ``seededFork_eq_recordedFork_of_reachable,
      ``Schnorr.LazySeed.toSeed_encode, ``Schnorr.LazySeed.fork_eq_recorded,
      ``Schnorr.LazySeed.fork_eq_seeded] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``defer_reset_run, ``seededFork_eq_recordedFork,
      ``seededFork_eq_recordedFork_of_reachable, ``Schnorr.LazySeed.fork_eq_seeded] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      unless conclusion.isAppOf ``Eq do
        throwError "{name}: must preserve a complete distribution"
      if (conclusion.find? (fun e => e.isConstOf ``instEvalDistSemanticsOfMonadLiftTSPMF)).isSome then
        throwError "{name}: statement must use native measure semantics"
      for param in params do
        let declaration ← getFVarLocalDecl param
        if declaration.userName == `I then
          for premise in params do
            let type ← inferType premise
            if (type.isAppOf ``Finite || type.isAppOf ``Fintype) &&
                (type.find? (fun e => e == param)).isSome then
              throwError "{name}: must not require a finite oracle-family universe"

end SignaturesTest.SeededLazyFork
