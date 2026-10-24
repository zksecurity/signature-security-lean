import Proofs.Runtime.Machine
import Proofs.Runtime.QueryCost
import Proofs.Runtime.SupportRefinement
import Proofs.Runtime.SamplingProbability

/-! Expose the closed machine's randomness as an adaptive oracle tree. Store
operations remain internal. Original execution budgets bound weighted sampling
paths and hence both the number and widths of reached random requests. -/

namespace Signatures.Runtime.MachineSampling

open OracleComp OracleSpec
open scoped ENNReal

abbrev spec (F : Type) : OracleSpec (Option Nat)
  | none => F
  | some n => Fin (n+1)

instance (F : Type) [Nonempty F] : (q : Option Nat) → Nonempty ((spec F).Range q)
  | none => inferInstance
  | some _ => inferInstance

def weight (sampling : Machine.SamplingCosts) : Option Nat → Nat
  | none => sampling.scalar+1
  | some n => sampling.uniform n+1

def effects (F G₁ G₂ K M : Type) (sampling : Machine.SamplingCosts) (storage : Ty CryptoAtom) :
    HandlerM (cryptoBase F G₁ G₂ K M) (Machine.Effect storage)
      (StateT (storage.Value (cryptoBase F G₁ G₂ K M)) (OracleComp (spec F))) := fun cmd arg state => match cmd with
  | .scalar => do
    let x ← (liftM ((spec F).query none) : OracleComp (spec F) F)
    pure (⟨x, sampling.scalar⟩, state)
  | .uniform n => do
    let x ← (liftM ((spec F).query (some n)) : OracleComp (spec F) (Fin (n+1)))
    pure (⟨x, sampling.uniform n⟩, state)
  | .read => pure (⟨state, 1⟩, state)
  | .write => pure (⟨(), 1⟩, arg)

theorem effects_queryCost (F G₁ G₂ K M : Type) (sampling : Machine.SamplingCosts)
    {storage a b} (cmd : Machine.Effect storage a b) (arg : a.Value (cryptoBase F G₁ G₂ K M))
    (state) (out : Run (b.Value (cryptoBase F G₁ G₂ K M)) × storage.Value (cryptoBase F G₁ G₂ K M))
    (n : Nat) (h : QueryCost (weight sampling) ((effects F G₁ G₂ K M sampling storage cmd arg).run state) out n) :
    n ≤ out.1.steps+1 := by
  cases cmd with
  | scalar =>
    change QueryCost (weight sampling) (PFunctor.FreeM.liftBind (P := (spec F).toPFunctor) none
      (fun x => pure (⟨x, sampling.scalar⟩, state))) out n at h
    cases h with
    | queryBind _ _ reply h => cases h; exact le_refl _
  | uniform m =>
    change QueryCost (weight sampling) (PFunctor.FreeM.liftBind (P := (spec F).toPFunctor) (some m)
      (fun x => pure (⟨x, sampling.uniform m⟩, state))) out n at h
    cases h with
    | queryBind _ _ reply h => cases h; exact le_refl _
  | read =>
    change QueryCost _ (pure (⟨state, 1⟩, state)) out n at h
    cases h
    change 0 ≤ 2
    decide
  | write =>
    change QueryCost _ (pure (⟨(), 1⟩, arg)) out n at h
    cases h
    change 0 ≤ 2
    decide

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq K] [DecidableEq M]

noncomputable def tree (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (code : Machine.Code Γ a) (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    OracleComp (spec F) (Run (a.Value (cryptoBase F G₁ G₂ K M))) := do
  let initial := code.init.run (arithmetic F G₁ G₂ K M cost) env
  let out ← (code.body.run (arithmetic F G₁ G₂ K M cost) (effects F G₁ G₂ K M sampling code.store) env).run
    initial.value
  pure ⟨out.1.value, initial.steps+out.1.steps+2⟩

omit [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq K] [DecidableEq M] in
theorem effects_support (sampling : Machine.SamplingCosts) (storage : Ty CryptoAtom)
    {a b} (cmd : Machine.Effect storage a b) (arg : a.Value (cryptoBase F G₁ G₂ K M)) :
    StateSupportRefines id (effects F G₁ G₂ K M sampling storage cmd arg)
      (Machine.effects sampling storage cmd arg) := by
  intro state out hout
  cases cmd with
  | scalar =>
    simp only [effects, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨x, _, rfl⟩ := hout
    simp only [Machine.effects, StateT.run, support_map, Set.mem_image]
    exact ⟨x, mem_support_uniformSample F, rfl⟩
  | uniform n =>
    simp only [effects, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨x, _, rfl⟩ := hout
    simp only [Machine.effects, StateT.run, support_map, Set.mem_image]
    exact ⟨x, mem_support_query _ _, rfl⟩
  | read =>
    simpa only [effects, Machine.effects, StateT.run, id_eq, support_pure, Set.mem_singleton_iff] using hout
  | write =>
    simpa only [effects, Machine.effects, StateT.run, id_eq, support_pure, Set.mem_singleton_iff] using hout

theorem tree_support (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (code : Machine.Code Γ a) (env : Env (cryptoBase F G₁ G₂ K M) Γ) (out)
    (hout : out ∈ support (tree cost sampling code env)) : out ∈ support (code.run cost sampling env) := by
  simp only [tree, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
  obtain ⟨body, hb, rfl⟩ := hout
  have h := code.body.run_support_refines (arithmetic F G₁ G₂ K M cost) id
    (effects F G₁ G₂ K M sampling code.store) (Machine.effects sampling code.store)
    (effects_support sampling code.store) env _ body hb
  simp only [Machine.Code.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
  exact ⟨body, h, rfl⟩

omit [SampleableType F] in
theorem tree_queryCost (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (code : Machine.Code Γ a) (env : Env (cryptoBase F G₁ G₂ K M) Γ) (out) (n : Nat)
    (h : QueryCost (weight sampling) (tree cost sampling code env) out n) : n ≤ out.steps := by
  simp only [tree] at h
  obtain ⟨body, c, final, hc, hfinal, hn⟩ := (QueryCost.bind_iff _ _ _ _ _).mp h
  cases hfinal
  have h := code.body.run_queryCost (arithmetic F G₁ G₂ K M cost) (weight sampling)
    (effects F G₁ G₂ K M sampling code.store) (effects_queryCost F G₁ G₂ K M sampling)
    env _ body c hc
  dsimp only
  omega

/-- No new query-count hypothesis: the original machine runtime certificate
already pays at least one unit for each reached sampling request. -/
theorem tree_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (code : Machine.Code Γ a) (env : Env (cryptoBase F G₁ G₂ K M) Γ) (B : Nat)
    (hb : ∀ out ∈ support (code.run cost sampling env), out.steps ≤ B) :
    IsQueryBound (tree cost sampling code env) B (fun q left => weight sampling q ≤ left)
      (fun q left => left-weight sampling q) := by
  apply QueryCost.isQueryBound
  intro out n h
  exact (tree_queryCost cost sampling code env out n h).trans
    (hb out (tree_support cost sampling code env out h.mem_support))

noncomputable def packageTree (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (pack : Machine.Package (cryptoBase F G₁ G₂ K M) Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) : OracleComp (spec F) (Run (a.Value (cryptoBase F G₁ G₂ K M))) :=
  (fun out => ⟨out.value, out.steps+(Env.load pack.data).steps+Γ.length+2⟩) <$>
    tree cost sampling pack.code (Env.append env pack.data)

theorem packageTree_support (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (pack : Machine.Package (cryptoBase F G₁ G₂ K M) Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (out)
    (hout : out ∈ support (packageTree cost sampling pack env)) : out ∈ support (pack.run cost sampling env) := by
  simp only [packageTree, support_map, Set.mem_image] at hout
  obtain ⟨source, hs, rfl⟩ := hout
  rw [Machine.Package.run_eq, support_map]
  exact Set.mem_image_of_mem _ (tree_support cost sampling pack.code _ source hs)

theorem packageTree_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (pack : Machine.Package (cryptoBase F G₁ G₂ K M) Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (B : Nat)
    (hb : ∀ out ∈ support (pack.run cost sampling env), out.steps ≤ B) :
    IsQueryBound (packageTree cost sampling pack env) B (fun q left => weight sampling q ≤ left)
      (fun q left => left-weight sampling q) := by
  apply QueryCost.isQueryBound
  intro out n h
  have hbudget := hb out (packageTree_support cost sampling pack env out h.mem_support)
  rw [packageTree, QueryCost.map_iff] at h
  obtain ⟨source, hs, rfl⟩ := h
  have hcost := tree_queryCost cost sampling pack.code _ source n hs
  dsimp only at hbudget
  omega

section Kernels

variable (r w k : Nat) [NeZero r]

noncomputable def real : (q : (spec (ZMod r)).Domain) → PMF ((spec (ZMod r)).Range q × Bool)
  | none => (PaddedSampling.decoded r w k).map (fun x => ((ZMod.finEquiv r) x.1, x.2))
  | some n => PaddedSampling.decoded (n+1) w k

noncomputable def ideal : QueryImpl (spec (ZMod r)) PMF
  | none => PMF.uniformOfFintype (ZMod r)
  | some n => PMF.uniformOfFintype (Fin (n+1))

theorem real_good (sampling : Machine.SamplingCosts) (B : Nat) (hB : B ≤ w)
    (hr : r ≤ 2^w) (hsampling : ∀ n, n < 2^(sampling.uniform n))
    (q : (spec (ZMod r)).Domain) (hq : weight sampling q ≤ B) :
    MarkedProbability.GoodLe (real r w k q) (ideal r q) := by
  cases q with
  | none =>
    have h := (PaddedSampling.decoded_good_le r w k hr).map (ZMod.finEquiv r)
    have he := PMF.uniformOfFintype_map_of_bijective (ZMod.finEquiv r) (ZMod.finEquiv r).bijective
    simpa only [real, ideal, he] using h
  | some n =>
    apply PaddedSampling.decoded_good_le
    have hw : sampling.uniform n ≤ w := by simp only [weight] at hq; omega
    have := (hsampling n).trans_le (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw)
    omega

theorem real_bad (sampling : Machine.SamplingCosts) (B : Nat) (hB : B ≤ w)
    (hr : r ≤ 2^w) (hsampling : ∀ n, n < 2^(sampling.uniform n))
    (q : (spec (ZMod r)).Domain) (hq : weight sampling q ≤ B) :
    MarkedProbability.bad (real r w k q) ≤ weight sampling q * (1/2 : ℝ≥0∞)^k := by
  have hsmall : MarkedProbability.bad (real r w k q) ≤ (1/2 : ℝ≥0∞)^k := by
    cases q with
    | none =>
      rw [real, MarkedProbability.bad_map]
      exact PaddedSampling.decoded_bad_le r w k hr
    | some n =>
      apply PaddedSampling.decoded_bad_le
      have hw : sampling.uniform n ≤ w := by simp only [weight] at hq; omega
      have := (hsampling n).trans_le (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw)
      omega
  apply hsmall.trans
  have hw : 1 ≤ weight sampling q := by cases q <;> simp [weight]
  have hw' : (1 : ℝ≥0∞) ≤ weight sampling q := by exact_mod_cast hw
  simpa only [one_mul] using mul_le_mul' hw' (le_refl ((1/2 : ℝ≥0∞)^k))

theorem probability {A : Type} (sampling : Machine.SamplingCosts) (B : Nat) (hB : B ≤ w)
    (hr : r ≤ 2^w) (hsampling : ∀ n, n < 2^(sampling.uniform n))
    (code : OracleComp (spec (ZMod r)) A)
    (hb : IsQueryBound code B (fun q left => weight sampling q ≤ left) (fun q left => left-weight sampling q)) :
    MarkedProbability.GoodLe (MarkedProbability.simulate (real r w k) code) (simulateQ (ideal r) code) ∧
      MarkedProbability.bad (MarkedProbability.simulate (real r w k) code) ≤ B*(1/2 : ℝ≥0∞)^k :=
  MarkedProbability.simulate_bound (real r w k) (ideal r) (weight sampling) B ((1/2 : ℝ≥0∞)^k)
    (real_good r w k sampling B hB hr hsampling) (real_bad r w k sampling B hB hr hsampling)
    code B (le_refl _) hb

end Kernels

end Signatures.Runtime.MachineSampling
