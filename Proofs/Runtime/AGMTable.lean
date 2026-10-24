import Proofs.Runtime.Machine
import Proofs.Runtime.SamplingState
import Proofs.Runtime.Table

/-! Full-domain AGM scalar initialization in the closed machine. The reference sampler
below contains only individual scalar draws. The target program uses Machine.Effect.scalar,
never a whole-function or whole-table sampling opcode. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.AGM

inductive Draw : Ty CryptoAtom → Ty CryptoAtom → Type
  | scalar : Draw .unit scalar

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

noncomputable def draws (sampling : Machine.SamplingCosts) :
    Handler (cryptoBase F G₁ G₂ K M) Draw unifSpec := fun .scalar _ =>
  (fun x => ⟨x, sampling.scalar⟩) <$> ($ᵗ F : ProbComp F)

theorem sampleTable_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (store : Ty CryptoAtom) (n : Nat) (state : store.Value (cryptoBase F G₁ G₂ K M)) :
    ((Signatures.Runtime.sampleTable (Machine.Effect.scalar (store := store))).run
      (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling store) (n, ())).run state =
      (fun r => (r, state)) <$> (Signatures.Runtime.sampleTable Draw.scalar).run
        (arithmetic F G₁ G₂ K M cost) (draws sampling) (n, ()) := by
  apply sampleTable_run_state
  intro s
  simp [draws, Machine.effects, StateT.run]

theorem sampleTable_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (store : Ty CryptoAtom) (n : Nat) (state : store.Value (cryptoBase F G₁ G₂ K M))
    (z : Run (List F) × store.Value (cryptoBase F G₁ G₂ K M))
    (hz : z ∈ support (((Signatures.Runtime.sampleTable (Machine.Effect.scalar (store := store))).run
      (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling store) (n, ())).run state)) :
    z.2 = state ∧ z.1.value.length = n ∧ z.1.steps ≤ n * (sampling.scalar + 17) + 10 := by
  rw [sampleTable_run] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  refine ⟨rfl, sampleTable_length _ _ _ _ _ hr, ?_⟩
  apply sampleTable_steps_le (arithmetic F G₁ G₂ K M cost) (draws sampling) Draw.scalar
    sampling.scalar ?_ n r hr
  intro out hout
  simp only [draws, support_map, Set.mem_image] at hout
  obtain ⟨x, _, rfl⟩ := hout
  exact le_rfl

theorem sampleTable_uniform (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (store : Ty CryptoAtom) (n : Nat) (state : store.Value (cryptoBase F G₁ G₂ K M)) :
    (fun z => z.1.value) <$>
      ((Signatures.Runtime.sampleTable (Machine.Effect.scalar (store := store))).run
        (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling store) (n, ())).run state =
      Vector.toList <$> SampleableType.vector F n := by
  rw [sampleTable_run]
  simp only [Functor.map_map]
  change Run.value <$> (Signatures.Runtime.sampleTable Draw.scalar).run
    (arithmetic F G₁ G₂ K M cost) (draws sampling) (n, ()) = _
  rw [Program.run_erase]
  exact Signatures.Runtime.sampleTable_uniform _ _ Draw.scalar (by simp [draws]) n

/-- Proof-only representation erasure gives exactly the full native function sampler.
The sample count is the entire finite domain, irrespective of source query budgets. -/
theorem sampleTable_function (ι : Type) [Fintype ι] [DecidableEq ι]
    (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (store : Ty CryptoAtom) (state : store.Value (cryptoBase F G₁ G₂ K M)) :
    (fun z => tableFunction (ι := ι) (0 : F) z.1.value) <$>
      ((Signatures.Runtime.sampleTable (Machine.Effect.scalar (store := store))).run
        (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling store) (Fintype.card ι, ())).run state =
      ($ᵗ (ι → F) : ProbComp (ι → F)) := by
  have h := congrArg (Functor.map (tableFunction (ι := ι) (0 : F)))
    (sampleTable_uniform cost sampling store (Fintype.card ι) state)
  rw [uniform_function_vector]
  simpa only [Functor.map_map, tableFunction_vector] using h

end Signatures.Runtime.AGM
