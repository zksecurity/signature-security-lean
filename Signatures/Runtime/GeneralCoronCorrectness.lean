import Signatures.Runtime.GeneralCoron

/-! Exact source correspondence for the general-caller BLS co-CDH runner.
The source interface only translates bounded randomness requests; it places no
arithmetic-language restriction on the caller's internal algorithm. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron

def generalSource {M G₁ : Type} (randomBound : Nat) :
    QueryImpl (generalSpec M G₁ randomBound) (OracleComp (BLS.ROM.advSpec M G₁))
  | .inl (.inl n) => liftM ((BLS.ROM.advSpec M G₁).query (.inl (.inl n.val)))
  | .inl (.inr m) => liftM ((BLS.ROM.advSpec M G₁).query (.inl (.inr m)))
  | .inr m => liftM ((BLS.ROM.advSpec M G₁).query (.inr m))

variable {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]

/-- Proof intermediary retaining the existing finite-list cache state. -/
noncomputable def generalCacheHandler (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) :
    GeneralCaller.Handler (spec := generalSpec M G₁ randomBound)
      (StateT (CacheState F M qS) ProbComp)
  | .inl (.inl n) => handler (G₂ := G₂) cost sampling g X h qS randomBound (.random n) ()
  | .inl (.inr m) => handler (G₂ := G₂) cost sampling g X h qS randomBound .hash m
  | .inr m => handler (G₂ := G₂) cost sampling g X h qS randomBound .sign m

theorem generalCacheHandler_machine (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) (i : GeneralRequest M randomBound) :
    StateRefines (machineState (F := F) (G₂ := G₂) (M := M) g X h)
      (Run.value <$> generalCacheHandler (G₂ := G₂) cost (machineSampling sampling qS)
        g X h qS randomBound i)
      (Run.value <$> generalHandler (F := F) (G₂ := G₂) cost sampling qS randomBound i) := by
  rcases i with (n | m) | m
  · exact machineHandler_refines cost sampling g X h qS randomBound (.random n) ()
  · exact machineHandler_refines cost sampling g X h qS randomBound .hash m
  · exact machineHandler_refines cost sampling g X h qS randomBound .sign m

theorem generalCacheHandler_native (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) (i : GeneralRequest M randomBound) :
    StateRefines CacheState.repr
      (Run.value <$> generalCacheHandler (G₂ := G₂) cost sampling g X h qS randomBound i)
      (simulateQ (nativeOracle (F := F) g X h qS) (generalSource randomBound i)) := by
  rcases i with (n | m) | m
  · exact handler_refines cost sampling g X h qS randomBound (.random n) ()
  · exact handler_refines cost sampling g X h qS randomBound .hash m
  · exact handler_refines cost sampling g X h qS randomBound .sign m

variable {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass C} {randomBound : Nat}
  {bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁)}

/-- The entire adaptive simulation, including the final wrapper state, agrees
with the source. The termination certificate excludes the `none` branch. -/
theorem generalSimulation_erase
    (R : GeneralCaller.Caller (Q := Q) (bd := bd))
    (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (pk : G₂) (qS fuel : Nat)
    (program : G₂ → OracleComp (generalSpec M G₁ randomBound) (M × G₁))
    (hprogram : R.machine.ImplementsWithin program fuel) (state : CacheState F M qS) :
    (fun p => (p.1.value, p.2)) <$>
      ((GeneralCaller.run R (generalHandler (F := F) (G₂ := G₂) cost sampling qS randomBound) fuel pk).run
        (machineState (F := F) (G₂ := G₂) (M := M) g X h state)) =
      (fun p => (some p.1, machineState (F := F) (G₂ := G₂) (M := M) g X h p.2)) <$>
        ((simulateQ (fun i => Run.value <$>
          generalCacheHandler (G₂ := G₂) cost (machineSampling sampling qS)
            g X h qS randomBound i) (program pk)).run state) := by
  have he := congrArg (fun c => c.run (machineState (F := F) (G₂ := G₂) (M := M) g X h state))
    (GeneralCaller.run_erase R (generalHandler (F := F) (G₂ := G₂) cost sampling qS randomBound) fuel pk program hprogram)
  simp only [StateT.run_map] at he
  have hs := GeneralCaller.simulateQ_refines (machineState (F := F) (G₂ := G₂) (M := M) g X h)
    (fun i => Run.value <$> generalCacheHandler (G₂ := G₂) cost (machineSampling sampling qS)
      g X h qS randomBound i)
    (fun i => Run.value <$> generalHandler (F := F) (G₂ := G₂) cost sampling qS randomBound i)
    (generalCacheHandler_machine cost sampling g X h qS randomBound) (program pk) state
  rw [← hs] at he
  simpa only [Functor.map_map] using he

/-- Final hashing and extraction commute with both cache representations, so
the completed general runner has the exact law of the native lazy reduction. -/
theorem generalReduction_erase_native
    (R : GeneralCaller.Caller (Q := Q) (bd := bd))
    (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (pk : G₂) (qS fuel : Nat)
    (program : G₂ → OracleComp (generalSpec M G₁ randomBound) (M × G₁))
    (hprogram : R.machine.ImplementsWithin program fuel) :
    Run.value <$> generalReduction (F := F) R cost sampling g X h pk qS fuel =
      some <$> nativeReduction (F := F) g X h qS
        (simulateQ (generalSource randomBound) (program pk)) := by
  let finishOption : Option (M × G₁) ×
      (machineStore qS).Value (cryptoBase F G₁ G₂ M M) → ProbComp (Option G₁) := fun p =>
    match p.1 with
    | none => pure none
    | some out => (fun r => some r.1.value) <$>
        (((machineFinish qS).run (arithmetic F G₁ G₂ M M cost)
          (Machine.effects sampling (machineStore qS)) (out, ())).run p.2)
  have hcost : Run.value <$> generalReduction (F := F) R cost sampling g X h pk qS fuel =
      ((fun p => (p.1.value, p.2)) <$>
        ((GeneralCaller.run R (generalHandler (F := F) (G₂ := G₂) cost sampling qS randomBound)
          fuel pk).run (machineState g X h .empty))) >>= finishOption := by
    simp only [generalReduction, map_bind, bind_map_left]
    congr 1
    funext p
    cases hv : p.1.value
    · simp [finishOption]
    · simp [finishOption]
  rw [hcost, generalSimulation_erase R cost sampling g X h pk qS fuel program hprogram,
    bind_map_left]
  have hn := GeneralCaller.simulateQ_refines CacheState.repr
    (fun i => Run.value <$> generalCacheHandler (G₂ := G₂) cost (machineSampling sampling qS)
      g X h qS randomBound i)
    (fun i => simulateQ (nativeOracle (F := F) g X h qS) (generalSource randomBound i))
    (generalCacheHandler_native cost (machineSampling sampling qS) g X h qS randomBound)
    (program pk) .empty
  have he : (CacheState.empty : CacheState F M qS).repr = ((fun _ => none, ∅), ∅) := rfl
  change _ = (simulateQ ((nativeOracle (F := F) g X h qS) ∘ₛ generalSource randomBound)
    (program pk)).run (CacheState.empty : CacheState F M qS).repr at hn
  rw [QueryImpl.simulateQ_compose, he] at hn
  simp only [nativeReduction, map_bind]
  rw [← hn, bind_map_left]
  congr 1
  funext p
  dsimp [finishOption]
  have hf := machineFinish_erase (G₂ := G₂) cost sampling g X h qS p.1 p.2
  rw [finish_erase] at hf
  simpa only [Functor.map_map] using congrArg (Functor.map some) hf

/-- Exact correspondence to the named co-CDH solver at every public key.
The premise identifies the caller, not the completed reduction. -/
theorem generalReduction_erase_original
    (R : GeneralCaller.Caller (Q := Q) (bd := bd))
    (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (g₂ pk : G₂) (qS fuel : Nat)
    (program : G₂ → OracleComp (generalSpec M G₁ randomBound) (M × G₁))
    (hprogram : R.machine.ImplementsWithin program fuel)
    (adv : BLS.ROM.AdversaryPK M G₁ G₂)
    (hsource : simulateQ (generalSource randomBound) (program pk) = adv pk) :
    Run.value <$> generalReduction (F := F) R cost sampling g X h pk qS fuel =
      some <$> BLS.CoCDH.coronReductionLazyPK (F := F) qS
        (BLS.ROM.cacheForgeryPK adv) g g₂ X pk h := by
  rw [generalReduction_erase_native R cost sampling g X h pk qS fuel program hprogram, hsource]
  rw [nativeReduction_original g X h g₂ pk qS adv]

/-- A total solver interface. Termination/source correspondence below proves
that the explicit cutoff default is never used by a certified caller. -/
noncomputable def generalSolverRun
    (R : GeneralCaller.Caller (Q := Q) (bd := bd))
    (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (pk : G₂) (qS fuel : Nat) : ProbComp (Run G₁) :=
  (fun r => ⟨r.value.getD 0, r.steps + 1⟩) <$>
    generalReduction (F := F) R cost sampling g X h pk qS fuel

theorem generalSolverRun_erase
    (R : GeneralCaller.Caller (Q := Q) (bd := bd))
    (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (g₂ pk : G₂) (qS fuel : Nat)
    (program : G₂ → OracleComp (generalSpec M G₁ randomBound) (M × G₁))
    (hprogram : R.machine.ImplementsWithin program fuel)
    (adv : BLS.ROM.AdversaryPK M G₁ G₂)
    (hsource : simulateQ (generalSource randomBound) (program pk) = adv pk) :
    Run.value <$> generalSolverRun (F := F) R cost sampling g X h pk qS fuel =
      BLS.CoCDH.coronReductionLazyPK (F := F) qS
        (BLS.ROM.cacheForgeryPK adv) g g₂ X pk h := by
  have he := congrArg (Functor.map (fun x : Option G₁ => x.getD 0))
    (generalReduction_erase_original (F := F) R cost sampling g X h g₂ pk qS fuel program hprogram adv hsource)
  simpa [generalSolverRun, Functor.map_map] using he

theorem generalSolverRun_bound
    (R : GeneralCaller.Caller (Q := Q) (bd := bd))
    (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (pk : G₂) (qS fuel localTime : Nat) (queries : Fin 3 → Nat)
    (hcaller : GeneralCaller.Budget R (generalReplies M G₁ randomBound) generalKind
      fuel pk localTime queries)
    (z : Run G₁)
    (hz : z ∈ support (generalSolverRun (F := F) R cost sampling g X h pk qS fuel)) :
    z.steps ≤ generalReductionBound cost sampling qS randomBound localTime queries + 1 := by
  simp only [generalSolverRun, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  exact Nat.add_le_add_right
    (generalReduction_bound R cost sampling g X h pk qS fuel localTime queries hcaller r hr) 1

end Signatures.Runtime.Coron
