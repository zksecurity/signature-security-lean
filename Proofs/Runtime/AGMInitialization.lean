import Proofs.Runtime.AGMTable
import Proofs.Runtime.TableRefinement

/-! Charged full-domain private keyed-table initialization. The sampler performs one scalar
draw per cell and the constructor executes indexed list lookup; neither is a whole-table
primitive. The input key enumeration remains fixed data loaded by the enclosing package. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.AGM

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))

variable {indexTy : Ty CryptoAtom}

def keyedValues : Expr CryptoOp [.list scalar, .list indexTy] (tableTy indexTy) :=
  .letE v0 (.letE v2 (.letE (.op .zero .unit)
    ((attachTable (indexTy := indexTy)).weakenTail [.list scalar, .list indexTy])))

def sampleKeyed (store : Ty CryptoAtom) (n : Nat) :
    Program CryptoOp (Machine.Effect store) [.list indexTy] (tableTy indexTy) :=
  .bind (.call (Signatures.Runtime.sampleTable Machine.Effect.scalar) (.cons (.nat n) .nil))
    (.ret keyedValues)

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

omit [SampleableType F] in
theorem keyedValues_run (cost : PrimitiveCosts) (values : List F)
    (keys : List (indexTy.Value (cryptoBase F G₁ G₂ K M))) :
    keyedValues.run (arithmetic F G₁ G₂ K M cost) (values, keys, ()) =
      let r := (attachTable (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost) (0, keys, values, ())
      ⟨r.value, r.steps + cost.field + 9⟩ := by
  have h := (attachTable (indexTy := indexTy)).weakenTail_run
    (Δ := [.list scalar, .list indexTy]) (arithmetic F G₁ G₂ K M cost)
    (0, keys, values, ()) (values, keys, ())
  simp only [Env.append] at h
  dsimp [arithmetic, CryptoOp.price] at h ⊢
  simp only [keyedValues, Expr.run, v0, v2, Var.get, Var.depth, h]
  apply congrArg (Run.mk _)
  omega

omit [SampleableType F] in
theorem keyedValues_value (cost : PrimitiveCosts) (values : List F)
    (keys : List (indexTy.Value (cryptoBase F G₁ G₂ K M))) :
    ((keyedValues (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost) (values, keys, ())).value =
      keys.mapIdx (fun n k => (k, (values[n]?).getD 0)) := by
  rw [keyedValues_run]
  exact attachTable_value (indexTy := indexTy) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost 0 keys values

theorem sampleKeyed_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (store : Ty CryptoAtom) (n : Nat) (keys : List (indexTy.Value (cryptoBase F G₁ G₂ K M)))
    (state : store.Value (cryptoBase F G₁ G₂ K M)) :
    ((sampleKeyed store n).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling store) (keys, ())).run state = (do
        let z ← ((Signatures.Runtime.sampleTable (Machine.Effect.scalar (store := store))).run
          (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling store) (n, ())).run state
        let r := (keyedValues (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost) (z.1.value, keys, ())
        pure (⟨r.value, z.1.steps + r.steps + n + 7⟩, z.2)) := by
  unfold sampleKeyed
  generalize (keyedValues (indexTy := indexTy)) = construct
  generalize (Signatures.Runtime.sampleTable (Machine.Effect.scalar (store := store))) = draw
  dsimp [Program.run, Args.run, Expr.run, StateT.run, StateT.bind, StateT.pure]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext z
  apply congrArg pure
  apply congrArg (fun r => (r, z.2))
  apply congrArg (Run.mk _)
  omega

def sampleKeyedBound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts) (n k : Nat) : Nat :=
  n * (sampling.scalar + 17) + k * (n * (2 * cost.natOp + 26) + cost.natOp + 63) + n + cost.field + 41

theorem sampleKeyed_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (store : Ty CryptoAtom) (n : Nat) (keys : List (indexTy.Value (cryptoBase F G₁ G₂ K M)))
    (state : store.Value (cryptoBase F G₁ G₂ K M))
    (z : Run ((tableTy indexTy).Value (cryptoBase F G₁ G₂ K M)) × store.Value (cryptoBase F G₁ G₂ K M))
    (hz : z ∈ support (((sampleKeyed store n).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling store) (keys, ())).run state)) :
    z.2 = state ∧ z.1.value.length = keys.length ∧ z.1.steps ≤ sampleKeyedBound cost sampling n keys.length := by
  rw [sampleKeyed_run] at hz
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  have hs := sampleTable_bound cost sampling store n state r hr
  refine ⟨hs.1, ?_, ?_⟩
  · simp only [keyedValues_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M), List.length_mapIdx]
  · have ha := attachTable_steps_le (indexTy := indexTy)
      (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost 0 keys r.1.value
    rw [hs.2.1] at ha
    simp only [keyedValues_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
    dsimp only [sampleKeyedBound]
    omega

theorem sampleKeyed_native {I : Type} [Fintype I] [DecidableEq I]
    (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts) (store : Ty CryptoAtom)
    (encode : I → indexTy.Value (cryptoBase F G₁ G₂ K M))
    (state : store.Value (cryptoBase F G₁ G₂ K M)) :
    (fun z => (z.1.value, z.2)) <$>
      (((sampleKeyed store (Fintype.card I)).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling store) (canonicalKeys encode, ())).run state) =
      (fun rho => (canonicalKeys (fun i => (encode i, rho i)), state)) <$> ($ᵗ (I → F) : ProbComp (I → F)) := by
  have h := congrArg (Functor.map (fun rho => (canonicalKeys (fun i => (encode i, rho i)), state)))
    (sampleTable_function I cost sampling store state)
  rw [sampleTable_run] at h
  rw [sampleKeyed_run, sampleTable_run]
  simp only [bind_pure_comp, Functor.map_map]
  simp only [keyedValues_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M), canonicalKeys_attach]
  simpa only [Functor.map_map, Function.comp_def] using h

theorem sampleKeyed_bind_native {I A : Type} [Fintype I] [DecidableEq I]
    (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts) (store : Ty CryptoAtom)
    (encode : I → indexTy.Value (cryptoBase F G₁ G₂ K M))
    (state : store.Value (cryptoBase F G₁ G₂ K M))
    (f : (tableTy indexTy).Value (cryptoBase F G₁ G₂ K M) →
      store.Value (cryptoBase F G₁ G₂ K M) → ProbComp A) :
    ((((sampleKeyed store (Fintype.card I)).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling store) (canonicalKeys encode, ())).run state) >>=
        fun z => f z.1.value z.2) =
      (($ᵗ (I → F) : ProbComp (I → F)) >>= fun rho =>
        f (canonicalKeys (fun i => (encode i, rho i))) state) := by
  have h := congrArg (fun comp => comp >>= fun z => f z.1 z.2)
    (sampleKeyed_native cost sampling store encode state)
  simpa only [bind_map_left] using h

end Signatures.Runtime.AGM
