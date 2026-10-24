/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.BLS.CoCDH.Spec.Assumption
import Proofs.BLS.CoCDH.LazyGame
import Proofs.BLS.CoCDH.LazyCoin
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# BLS EUF-CMA ⇒ co-CDH — the `q_S` Coron partitioning bound

**Coron's partitioning** loses the signing-query count `q_S`: at every fresh hash query flip an
independent biased coin `c ∈ {0,1}` with
`Pr[c = 1] = δ` and set

  `H(m) = ρ_m·g₁ + c_m·h`   (a fresh `ρ_m ← $ᵗF`, the co-CDH challenge `h` added iff `c_m = 1`).

Because `ρ_m·g₁` is already uniform (`hgen`), adding the fixed shift `c_m·h` keeps `H(m)` uniform, so
the coin is *hidden* from the adversary — its view is independent of the coins.

* Signing `m` with `c_m = 0`:  `x·H(m) = ρ_m·(x·g₁) = ρ_m·X₁` — computable from the public `X₁ = x·g₁`.
* Signing `m` with `c_m = 1`:  needs `x·h` — abort.
* A forgery `(m*, σ*)` on a `c_{m*} = 1` message that was never signed gives
  `σ* = x·H(m*) = ρ_{m*}·X₁ + x·h`, hence `x·h = σ* − ρ_{m*}·X₁` — the co-CDH answer (`coron_extract`).

The reduction wins whenever every *signed* message drew `c = 0` (so no abort) and the *forgery* message
drew `c = 1`.  As the coins are independent of the (view-determined) run, this happens with probability
`δ·(1−δ)^{|signed|} ≥ δ·(1−δ)^{q_S}`, giving `Adv^{EUF-CMA} ≤ (δ·(1−δ)^{q_S})⁻¹ · Adv^{co-CDH}`
(optimized at `δ = 1/(q_S+1)`, this is the `≈ e·(q_S+1)` Coron bound).
-/

open BLS.ROM

open BilinearGroup

namespace BLS.CoCDH.Coron

open BLS.CoCDH.Tight

variable {F M G₁ G₂ Gₜ : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]

/-- **Coron extraction: a forgery on a challenge-embedded (`c = 1`) message is a co-CDH solution.**
With public key `pk = x·g₂`, `X₁ = x·g₁`, and the random-oracle image of the forgery message programmed
to `H(m*) = ρ·g₁ + h`, any signature `σ` that verifies (`e(σ, g₂) = e(ρ·g₁ + h, pk)`) yields
`σ − ρ·X₁ = x·h` — exactly the co-CDH answer.  From left non-degeneracy of the pairing and `smul`
bilinearity. -/
theorem coron_extract (g₁ : G₁) (g₂ : G₂) (x ρ : F) (h σ X₁ : G₁) (hX : X₁ = x • g₁)
    (hinj : Function.Injective (fun z : G₁ => pairing (F := F) (Gₜ := Gₜ) z g₂))
    (hver : pairing (F := F) (Gₜ := Gₜ) σ g₂
      = pairing (F := F) (Gₜ := Gₜ) (ρ • g₁ + h) (x • g₂)) :
    σ - ρ • X₁ = x • h := by
  have hσ : σ = x • (ρ • g₁ + h) := by
    apply hinj; dsimp only
    rw [hver, pairing_smul_right, pairing_smul_left]
  rw [hσ, hX, smul_add, smul_smul, smul_smul, mul_comm]
  abel

open OracleComp OracleSpec

variable [Fintype M] [DecidableEq M] [SampleableType F] [Fintype F] [DecidableEq G₁]

/-- **Pushforward-bind congruence.**  If the first factor's *projected* distribution matches (`hstep`)
and each continuation's projected distribution matches on the projected state (`hcont`), then the whole
projected bind matches.  The projection `proj` on the state is a deterministic map (identity on the
output), so relating the two computations is a pushforward — the bind respects it.  This is the engine
that lifts the per-step projections (`realCoronK_step_proj_inl/inr`) to whole runs. -/
lemma evalSPMF_bind_proj_congr {β σ σ' γ : Type} (proj : σ → σ')
    (m1 : ProbComp (β × σ)) (m2 : ProbComp (β × σ'))
    (g1 : β → σ → ProbComp (γ × σ)) (g2 : β → σ' → ProbComp (γ × σ'))
    (hstep : 𝒮[m1 >>= fun z => pure (z.1, proj z.2)] = 𝒮[m2])
    (hcont : ∀ b s, 𝒮[g1 b s >>= fun z => pure (z.1, proj z.2)] = 𝒮[g2 b (proj s)]) :
    𝒮[(m1 >>= fun p => g1 p.1 p.2) >>= fun z => pure (z.1, proj z.2)]
      = 𝒮[m2 >>= fun p => g2 p.1 p.2] := by
  rw [bind_assoc, evalSPMF_bind_congr' m1 (fun p => hcont p.1 p.2)]
  have hrw : (m1 >>= fun p => g2 p.1 (proj p.2))
      = (m1 >>= fun p => pure (p.1, proj p.2)) >>= fun p' => g2 p'.1 p'.2 := by
    rw [bind_assoc]; simp only [pure_bind]
  rw [hrw, evalSPMF_bind (m1 >>= fun p => pure (p.1, proj p.2)), evalSPMF_bind m2, hstep]

/-- A fixed-public-key Coron BLS computation with private uniform randomness, hash queries, and
signing queries.  The public-key-aware proof instantiates this computation pointwise. -/
abbrev CoronAdv (M G₁ : Type) := Adversary M G₁

/-- A public-key-indexed family of Coron adversaries. -/
abbrev CoronAdvPK (M G₁ G₂ : Type) := G₂ → CoronAdv M G₁

/-! ## The coin partitioning

The finite **analysis game** samples a whole coin function `k : M → Fin (q_S+1)` up front
(`c_m := (k m = 0)`, `Pr[c_m = 1] = 1/(q_S+1) = δ`).  This exposes the joint distribution needed by
the counting argument: for fixed `k` the run factors, `coin_partition` applies directly, and the
per-`k` coupling is a fixed translation.  The public reduction defined below uses a lazy coin cache;
`evalSPMF_lazyCoin_eq_table` proves that it has exactly this analysis distribution. -/

/-- **Eager-coin Coron oracle** (state = the real dlog cache).  Coin `c_m = (k m = 0)` is read from the
fixed coin function `k`; the dlog is lazy via `BLS.ROM.Internal.getDlogS`.  Hash `m`: `ρ·g₁ + c_m·h`.  Sign `m`: abort
(`0`) if `c_m = 1`, else `ρ·X₁`. -/
noncomputable def coronOracleK (g₁ X₁ h : G₁) (qS : ℕ) (k : M → Fin (qS + 1)) :
    QueryImpl (advSpec M G₁) (StateT ((M → Option F) × Finset M) ProbComp) :=
  fun q => match q with
    | Sum.inl (Sum.inl n) =>
        (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
          StateT ((M → Option F) × Finset M) ProbComp (Fin (n + 1)))
    | Sum.inl (Sum.inr m) => do
        let ρ ← BLS.ROM.Internal.getDlogS (F := F) m
        pure (ρ • g₁ + (if k m = 0 then h else 0))
    | Sum.inr m => do
        modify (fun s => (s.1, insert m s.2))
        let ρ ← BLS.ROM.Internal.getDlogS (F := F) m
        pure (if k m = 0 then (0 : G₁) else ρ • X₁)

/-- **Eager-coin analysis companion** (signs everything, using `xh = x·h`). -/
noncomputable def realCoronK (g₁ X₁ h xh : G₁) (qS : ℕ) (k : M → Fin (qS + 1)) :
    QueryImpl (advSpec M G₁) (StateT ((M → Option F) × Finset M) ProbComp) :=
  fun q => match q with
    | Sum.inl (Sum.inl n) =>
        (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
          StateT ((M → Option F) × Finset M) ProbComp (Fin (n + 1)))
    | Sum.inl (Sum.inr m) => do
        let ρ ← BLS.ROM.Internal.getDlogS (F := F) m
        pure (ρ • g₁ + (if k m = 0 then h else 0))
    | Sum.inr m => do
        modify (fun s => (s.1, insert m s.2))
        let ρ ← BLS.ROM.Internal.getDlogS (F := F) m
        pure (ρ • X₁ + (if k m = 0 then xh else 0))

/-- Eager bad event: some *signed* message drew the challenge coin (`k m = 0`, i.e. `c_m = 1`). -/
def signedC1K (qS : ℕ) (k : M → Fin (qS + 1)) (st : (M → Option F) × Finset M) : Prop :=
  ∃ m ∈ st.2, k m = 0

/-- **Full-table Coron analysis reduction.**  On co-CDH input `X₂ = x·g₂`, run the member of the
adversary family indexed by exactly that public key.  The headline theorem exposes
`coronReductionLazyPK`; this definition is its distributionally equivalent counting game. -/
noncomputable def coronReductionKPK (qS : ℕ) (adv : CoronAdvPK M G₁ G₂) :
    CoCDHAdversary F G₁ G₂ :=
  fun g₁ _g₂ X₁ X₂ h => do
    let k ← ($ᵗ (M → Fin (qS + 1)) : ProbComp (M → Fin (qS + 1)))
    let ((mstar, σstar), st) ←
      (simulateQ (coronOracleK (F := F) g₁ X₁ h qS k) (adv X₂)).run ((fun _ => none), ∅)
    pure (σstar - ((st.1 mstar).getD 0) • X₁)

/-! ## Lazy reduction implementation

The full function `k` above is retained as the finite counting game used by the proof.  The actual
reduction below instead exposes coin draws as queries to a second random oracle.  Its cache starts
empty, so only messages reached by the adversary allocate a coin.
-/

omit [Fintype M] [DecidableEq M] [Fintype F] [DecidableEq G₁] in
private lemma coinTableImpl_query (qS : ℕ) (k : M → Fin (qS + 1)) (m : M) :
    simulateQ (coinTableImpl k)
        (liftM ((M →ₒ Fin (qS + 1)).query m) :
          OracleComp (unifSpec + (M →ₒ Fin (qS + 1))) (Fin (qS + 1))) =
      pure (k m) := by
  change simulateQ (coinTableImpl k)
    (liftM (liftM ((M →ₒ Fin (qS + 1)).query m) :
      OracleQuery (unifSpec + (M →ₒ Fin (qS + 1))) (Fin (qS + 1)))) = pure (k m)
  simp [coinTableImpl, simulateQ_query]
  change (pure (k m) : ProbComp (Fin (qS + 1))) = pure (k m)
  rfl

omit [Fintype M] [DecidableEq M] [Fintype F] [DecidableEq G₁] in
private lemma coinTableImpl_liftProb (qS : ℕ) (k : M → Fin (qS + 1)) {α : Type}
    (mx : ProbComp α) :
    simulateQ (coinTableImpl k)
        (liftM mx : OracleComp (unifSpec + (M →ₒ Fin (qS + 1))) α) = mx := by
  simp [coinTableImpl, QueryImpl.simulateQ_add_liftM_left]

omit [Fintype M] [Fintype F] [DecidableEq G₁] in
/-- With a fixed coin table, one lazy-Coron oracle step is exactly the original table-analysis
step. -/
lemma coronOracleLazy_table_step (g₁ X₁ h : G₁) (qS : ℕ)
    (k : M → Fin (qS + 1)) (q : (advSpec M G₁).Domain)
    (s : (M → Option F) × Finset M) :
    simulateQ (coinTableImpl k) ((coronOracleLazy (F := F) g₁ X₁ h qS q).run s) =
      (coronOracleK (F := F) g₁ X₁ h qS k q).run s := by
  rcases q with (n | m) | m
  · simp [coronOracleLazy, coronOracleK, coinTableImpl]
  · simp [coronOracleLazy, coronOracleK, coinTableImpl_query, coinTableImpl_liftProb]
  · simp [coronOracleLazy, coronOracleK, coinTableImpl_query, coinTableImpl_liftProb]

omit [Fintype M] [Fintype F] [DecidableEq G₁] in
/-- The fixed-table step bridge lifts to an arbitrary adaptive Coron adversary. -/
lemma coronOracleLazy_table_run (g₁ X₁ h : G₁) (qS : ℕ)
    (k : M → Fin (qS + 1)) {α : Type}
    (oa : OracleComp (advSpec M G₁) α)
    (s : (M → Option F) × Finset M) :
    simulateQ (coinTableImpl k)
        ((simulateQ (coronOracleLazy (F := F) g₁ X₁ h qS) oa).run s) =
      (simulateQ (coronOracleK (F := F) g₁ X₁ h qS k) oa).run s := by
  exact simulateQ_StateT_compose
    (coronOracleLazy (F := F) g₁ X₁ h qS) (coinTableImpl k)
    (coronOracleK (F := F) g₁ X₁ h qS k)
    (coronOracleLazy_table_step g₁ X₁ h qS k) oa s

omit [Fintype M] [Fintype F] [DecidableEq G₁] [AddCommGroup G₂] [Module F G₂] in
/-- Interpreting the reduction program with a fixed coin table produces the table-analysis
reduction run for that same table. -/
lemma coronReductionProgram_table (g₁ X₁ : G₁) (X₂ : G₂) (h : G₁) (qS : ℕ)
    (adv : CoronAdvPK M G₁ G₂) (k : M → Fin (qS + 1)) :
    simulateQ (coinTableImpl k)
        (coronReductionProgram (F := F) g₁ X₁ X₂ h qS adv) =
      (do
        let ((mstar, σstar), st) ←
          (simulateQ (coronOracleK (F := F) g₁ X₁ h qS k) (adv X₂)).run
            ((fun _ => none), ∅)
        pure (σstar - ((st.1 mstar).getD 0) • X₁)) := by
  simp only [coronReductionProgram, simulateQ_bind]
  rw [coronOracleLazy_table_run g₁ X₁ h qS k]
  simp

omit [Fintype F] [DecidableEq G₁] [AddCommGroup G₂] [Module F G₂] in
/-- The lazy reduction and the full-table analysis reduction have exactly the same output
distribution on every co-CDH input. -/
theorem coronReductionLazyPK_evalSPMF (g₁ : G₁) (g₂ : G₂) (X₁ : G₁) (X₂ : G₂) (h : G₁)
    (qS : ℕ) (adv : CoronAdvPK M G₁ G₂) :
    𝒮[coronReductionLazyPK (F := F) qS adv g₁ g₂ X₁ X₂ h] =
      𝒮[coronReductionKPK (F := F) qS adv g₁ g₂ X₁ X₂ h] := by
  classical
  rw [coronReductionLazyPK, evalSPMF_lazyCoin_eq_table]
  simp only [tableExtending_empty, coronReductionKPK]
  refine congrArg evalSPMF ?_
  refine bind_congr fun k => ?_
  exact coronReductionProgram_table g₁ X₁ X₂ h qS adv k

omit [Fintype F] in
/-- Replacing the table-analysis reduction by the lazy reduction leaves the co-CDH experiment's
entire output distribution unchanged. -/
theorem coCDHExp_coronReductionLazyPK_evalSPMF [SampleableType G₁]
    (g₁ : G₁) (g₂ : G₂) (qS : ℕ) (adv : CoronAdvPK M G₁ G₂) :
    𝒮[coCDHExp (F := F) g₁ g₂ (coronReductionLazyPK qS adv)] =
      𝒮[coCDHExp (F := F) g₁ g₂ (coronReductionKPK qS adv)] := by
  unfold coCDHExp
  refine evalSPMF_bind_congr' _ fun x => ?_
  refine evalSPMF_bind_congr' _ fun h => ?_
  rw [evalSPMF_bind, evalSPMF_bind,
    coronReductionLazyPK_evalSPMF g₁ g₂ (x • g₁) (x • g₂) h qS adv]

omit [Fintype M] [Fintype F] [DecidableEq G₁] in
/-- The appended verification-hash query preserves the signed set and leaves the forgery message
cached. -/
lemma cacheForgery_run_support (g₁ X₁ : G₁) (adv : CoronAdv M G₁) (qS : ℕ)
    (hqs : ∀ out ∈ support
      ((simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ X₁) adv).run ((fun _ => none), ∅)),
      out.2.2.card ≤ qS) :
    ∀ out ∈ support
      ((simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ X₁) (cacheForgery adv)).run
        ((fun _ => none), ∅)),
      out.2.2.card ≤ qS ∧ (out.2.1 out.1.1).isSome := by
  intro out hout
  simp only [cacheForgery, simulateQ_bind, StateT.run_bind, support_bind,
    Set.mem_iUnion, exists_prop] at hout
  obtain ⟨w, hw, hout⟩ := hout
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
  obtain ⟨p, hp, hout⟩ := hout
  subst hout
  have hp' : p ∈ support
      ((BLS.ROM.Internal.oracle (F := F) g₁ X₁ (Sum.inl (Sum.inr w.1.1))).run w.2) := by
    rw [show simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ X₁)
        (liftM ((advSpec M G₁).query (Sum.inl (Sum.inr w.1.1))) :
          OracleComp (advSpec M G₁) G₁) =
        BLS.ROM.Internal.oracle (F := F) g₁ X₁ (Sum.inl (Sum.inr w.1.1)) by simp] at hp
    exact hp
  obtain ⟨hsigned, hcached⟩ := realOracle_hash_state g₁ X₁ w.1.1 w.2 p hp'
  refine ⟨?_, hcached⟩
  rw [hsigned]
  exact hqs w hw

omit [Fintype M] [Fintype F] [DecidableEq G₁] in
/-- The eager sign step always inserts `m` into the signed set. -/
lemma mem_signed_of_inr_K_coron (g₁ X₁ h : G₁) (qS : ℕ) (k : M → Fin (qS + 1)) (m : M)
    (s : (M → Option F) × Finset M) :
    ∀ z ∈ support ((coronOracleK (F := F) g₁ X₁ h qS k (Sum.inr m)).run s), m ∈ z.2.2 := by
  intro z hz
  simp only [coronOracleK, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
    mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  simp [getDlogS_snd_preserved m (s.1, insert m s.2) w hw]

omit [Fintype M] [Fintype F] [DecidableEq G₁] in
lemma mem_signed_of_inr_K_real (g₁ X₁ h xh : G₁) (qS : ℕ) (k : M → Fin (qS + 1)) (m : M)
    (s : (M → Option F) × Finset M) :
    ∀ z ∈ support ((realCoronK (F := F) g₁ X₁ h xh qS k (Sum.inr m)).run s), m ∈ z.2.2 := by
  intro z hz
  simp only [realCoronK, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
    mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  simp [getDlogS_snd_preserved m (s.1, insert m s.2) w hw]

omit [Field F] [AddCommGroup G₁] [Module F G₁] [Fintype M] [DecidableEq M]
  [SampleableType F] [Fintype F] [DecidableEq G₁] in
/-- **Run-level persistence of `signedC1K`.**  Once a signed message drew the challenge coin, it stays
(the signed set only grows, `k` is fixed). -/
lemma run_preserves_signedC1K (qS : ℕ) (k : M → Fin (qS + 1))
    {O : QueryImpl (advSpec M G₁) (StateT ((M → Option F) × Finset M) ProbComp)}
    (hmono : ∀ (q : (advSpec M G₁).Domain) (s : (M → Option F) × Finset M)
        (z : (advSpec M G₁).Range q × (M → Option F) × Finset M),
        z ∈ support ((O q).run s) → s.2 ⊆ z.2.2)
    {α : Type} (adv : OracleComp (advSpec M G₁) α) :
    ∀ (s : (M → Option F) × Finset M), signedC1K qS k s →
      ∀ z ∈ support ((simulateQ O adv).run s), signedC1K qS k z.2 := by
  apply simulateQ_run_preservesInv O (signedC1K qS k) ?_ adv
  rintro q s ⟨m, hm, hcoin⟩ z hz
  exact ⟨m, hmono q s z hz hm, hcoin⟩

omit [Fintype M] [Fintype F] [DecidableEq G₁] in
/-- Signed-set monotonicity for `coronOracleK`. -/
lemma coronOracleK_signed_mono (g₁ X₁ h : G₁) (qS : ℕ) (k : M → Fin (qS + 1))
    (q : (advSpec M G₁).Domain)
    (s : (M → Option F) × Finset M) :
    ∀ z ∈ support ((coronOracleK (F := F) g₁ X₁ h qS k q).run s), s.2 ⊆ z.2.2 := by
  rcases q with (n | m) | m
  · intro z hz
    simp [coronOracleK] at hz
    rcases hz with ⟨u, rfl⟩
    rfl
  all_goals
    intro z hz
    simp only [coronOracleK, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      mem_support_bind_iff, mem_support_pure_iff] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simp [getDlogS_snd_preserved _ _ w hw]

omit [Fintype M] [Fintype F] [DecidableEq G₁] in
/-- Signed-set monotonicity for `realCoronK`. -/
lemma realCoronK_signed_mono (g₁ X₁ h xh : G₁) (qS : ℕ) (k : M → Fin (qS + 1))
    (q : (advSpec M G₁).Domain)
    (s : (M → Option F) × Finset M) :
    ∀ z ∈ support ((realCoronK (F := F) g₁ X₁ h xh qS k q).run s), s.2 ⊆ z.2.2 := by
  rcases q with (n | m) | m
  · intro z hz
    simp [realCoronK] at hz
    rcases hz with ⟨u, rfl⟩
    rfl
  all_goals
    intro z hz
    simp only [realCoronK, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      mem_support_bind_iff, mem_support_pure_iff] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simp [getDlogS_snd_preserved _ _ w hw]

omit [Fintype M] [Fintype F] [DecidableEq G₁] in
/-- Off the coin (`k m ≠ 0`), the eager sign steps of `coronOracleK` and `realCoronK` coincide. -/
lemma coronK_inr_eq_off_coin (g₁ X₁ h xh : G₁) (qS : ℕ) (k : M → Fin (qS + 1)) (m : M)
    (hk : k m ≠ 0) (s : (M → Option F) × Finset M) :
    (coronOracleK (F := F) g₁ X₁ h qS k (Sum.inr m)).run s
      = (realCoronK (F := F) g₁ X₁ h xh qS k (Sum.inr m)).run s := by
  simp only [coronOracleK, realCoronK, if_neg hk, add_zero]

omit [Fintype M] [Fintype F] [DecidableEq G₁] in
/-- **Coupling B′ (eager), general form.**  Same coupling for any event `Q` that entails `¬signedC1K`
(so it may read the cache, e.g. the verification predicate). -/
theorem coupling_coron_realCoron_K_gen (g₁ X₁ h xh : G₁) (qS : ℕ) (k : M → Fin (qS + 1)) {α : Type}
    (adv : OracleComp (advSpec M G₁) α)
    (Q : α × ((M → Option F) × Finset M) → Prop) (hQ : ∀ z, Q z → ¬ signedC1K qS k z.2) :
    ∀ s : (M → Option F) × Finset M,
      Pr[Q | (simulateQ (coronOracleK (F := F) g₁ X₁ h qS k) adv).run s]
      = Pr[Q | (simulateQ (realCoronK (F := F) g₁ X₁ h xh qS k) adv).run s] := by
  induction adv using OracleComp.inductionOn with
  | pure x => intro s; simp only [simulateQ_pure, StateT.run_pure]
  | query_bind q k' ih =>
      intro s
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      rcases q with (n | m) | m
      ·
          have houter : (coronOracleK (F := F) g₁ X₁ h qS k (Sum.inl (Sum.inl n))).run s
                      = (realCoronK (F := F) g₁ X₁ h xh qS k
                          (Sum.inl (Sum.inl n))).run s := rfl
          rw [houter, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
          exact tsum_congr fun p => by rw [ih p.1 p.2]
      ·
          have houter : (coronOracleK (F := F) g₁ X₁ h qS k
                          (Sum.inl (Sum.inr m))).run s
                      = (realCoronK (F := F) g₁ X₁ h xh qS k
                          (Sum.inl (Sum.inr m))).run s := by
            rfl
          rw [houter, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
          exact tsum_congr fun p => by rw [ih p.1 p.2]
      ·
          by_cases hk : k m = 0
          · rw [probEvent_eq_zero (by
                intro z hz
                rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
                obtain ⟨p, hp, hz⟩ := hz
                have hsig : signedC1K qS k p.2 :=
                  ⟨m, mem_signed_of_inr_K_coron g₁ X₁ h qS k m s p hp, hk⟩
                exact fun hev => hQ z hev (run_preserves_signedC1K qS k
                  (coronOracleK_signed_mono g₁ X₁ h qS k) (k' p.1) p.2 hsig z hz)),
              probEvent_eq_zero (by
                intro z hz
                rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
                obtain ⟨p, hp, hz⟩ := hz
                have hsig : signedC1K qS k p.2 :=
                  ⟨m, mem_signed_of_inr_K_real g₁ X₁ h xh qS k m s p hp, hk⟩
                exact fun hev => hQ z hev (run_preserves_signedC1K qS k
                  (realCoronK_signed_mono g₁ X₁ h xh qS k) (k' p.1) p.2 hsig z hz))]
          · rw [coronK_inr_eq_off_coin g₁ X₁ h xh qS k m hk s,
              probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
            exact tsum_congr fun p => by rw [ih p.1 p.2]

/-- **Eager coin-erasing projection** (fixed `k`): collapse each cached dlog `ρ_m ↦ ρ_m + c_m·ρ_h`,
`c_m = (k m = 0)`, turning `realCoronK`'s cache into the real game's. -/
def projCK (ρh : F) (qS : ℕ) (k : M → Fin (qS + 1)) (st : (M → Option F) × Finset M) :
    (M → Option F) × Finset M :=
  (fun m => (st.1 m).map (fun ρ => ρ + (if k m = 0 then ρh else 0)), st.2)

omit [Fintype M] [SampleableType F] [Fintype F] in
lemma projCK_update (ρh : F) (qS : ℕ) (k : M → Fin (qS + 1)) (cache : M → Option F)
    (signed : Finset M) (m : M) (ρ : F) :
    projCK ρh qS k (Function.update cache m (some ρ), signed)
      = (Function.update (projCK ρh qS k (cache, signed)).1 m (some (ρ + (if k m = 0 then ρh else 0))),
          signed) := by
  refine Prod.ext ?_ rfl
  funext m'
  by_cases hm : m' = m
  · subst hm; simp only [projCK, Function.update_self, Option.map_some]
  · simp only [projCK, Function.update_of_ne hm]

omit [Fintype M] [Fintype F] [DecidableEq G₁] in
/-- **Coupling A′ eager, private-randomness step.**  Both games forward the same uniform query and
leave the state unchanged, so projection commutes with the step. -/
lemma realCoronK_step_proj_unif (g₁ X₁ h xh : G₁) (ρh : F) (qS : ℕ)
    (k : M → Fin (qS + 1)) (n : ℕ) (s : (M → Option F) × Finset M) :
    𝒮[(realCoronK (F := F) g₁ X₁ h xh qS k (Sum.inl (Sum.inl n))).run s >>=
        fun z => pure (z.1, projCK ρh qS k z.2)]
      = 𝒮[(BLS.ROM.Internal.oracle (F := F) g₁ X₁ (Sum.inl (Sum.inl n))).run
          (projCK ρh qS k s)] := by
  simp [realCoronK, BLS.ROM.Internal.oracle, StateT.run_monadLift]

omit [Fintype M] [Fintype F] [DecidableEq G₁] in
/-- **Coupling A′ eager, hash step.** -/
lemma realCoronK_step_proj_inl (g₁ X₁ h xh : G₁) (ρh : F) (qS : ℕ) (k : M → Fin (qS + 1)) (m : M)
    (hh : h = ρh • g₁) (s : (M → Option F) × Finset M) :
    𝒮[(realCoronK (F := F) g₁ X₁ h xh qS k (Sum.inl (Sum.inr m))).run s >>=
        fun z => pure (z.1, projCK ρh qS k z.2)]
      = 𝒮[(BLS.ROM.Internal.oracle (F := F) g₁ X₁ (Sum.inl (Sum.inr m))).run
          (projCK ρh qS k s)] := by
  have hval : ∀ ρ : F, ρ • g₁ + (if k m = 0 then h else (0 : G₁))
      = (ρ + (if k m = 0 then ρh else 0)) • g₁ := by
    intro ρ; rw [hh]; by_cases hk : k m = 0 <;> simp [hk, add_smul]
  have hL : ((realCoronK (F := F) g₁ X₁ h xh qS k (Sum.inl (Sum.inr m))).run s
        >>= fun z => pure (z.1, projCK ρh qS k z.2))
      = ((BLS.ROM.Internal.getDlogS (F := F) m).run s >>= fun w =>
          pure (w.1 • g₁ + (if k m = 0 then h else 0), projCK ρh qS k w.2)) := by
    simp only [realCoronK, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  have hR : (BLS.ROM.Internal.oracle (F := F) g₁ X₁ (Sum.inl (Sum.inr m))).run (projCK ρh qS k s)
      = (BLS.ROM.Internal.getDlogS (F := F) m).run (projCK ρh qS k s) >>= fun v => pure (v.1 • g₁, v.2) := by
    simp only [BLS.ROM.Internal.oracle, StateT.run_bind, StateT.run_pure]
  rw [hL, hR, getDlogS_run, getDlogS_run,
    show (projCK ρh qS k s).1 m = (s.1 m).map (fun ρ => ρ + (if k m = 0 then ρh else 0)) from rfl]
  cases hsm : s.1 m with
  | some ρ => simp only [Option.map_some, pure_bind, hval, projCK]
  | none =>
      simp only [Option.map_none, bind_assoc, pure_bind, hval, projCK_update]
      exact evalSPMF_ext (probOutput_bind_add_right_uniform F (if k m = 0 then ρh else 0)
        (fun v => pure (v • g₁, (Function.update (projCK ρh qS k s).1 m (some v), s.2))))

omit [Fintype M] [Fintype F] [DecidableEq G₁] in
/-- **Coupling A′ eager, sign step.** -/
lemma realCoronK_step_proj_inr (g₁ X₁ h xh : G₁) (ρh : F) (qS : ℕ) (k : M → Fin (qS + 1)) (m : M)
    (hxh : xh = ρh • X₁) (s : (M → Option F) × Finset M) :
    𝒮[(realCoronK (F := F) g₁ X₁ h xh qS k (Sum.inr m)).run s >>= fun z => pure (z.1, projCK ρh qS k z.2)]
      = 𝒮[(BLS.ROM.Internal.oracle (F := F) g₁ X₁ (Sum.inr m)).run (projCK ρh qS k s)] := by
  have hval : ∀ ρ : F, ρ • X₁ + (if k m = 0 then xh else (0 : G₁))
      = (ρ + (if k m = 0 then ρh else 0)) • X₁ := by
    intro ρ; rw [hxh]; by_cases hk : k m = 0 <;> simp [hk, add_smul]
  have hL : ((realCoronK (F := F) g₁ X₁ h xh qS k (Sum.inr m)).run s
        >>= fun z => pure (z.1, projCK ρh qS k z.2))
      = ((BLS.ROM.Internal.getDlogS (F := F) m).run (s.1, insert m s.2) >>= fun w =>
          pure (w.1 • X₁ + (if k m = 0 then xh else 0), projCK ρh qS k w.2)) := by
    simp only [realCoronK, StateT.run_bind, StateT.run_modify, StateT.run_pure, bind_assoc,
      pure_bind]
  have hR : (BLS.ROM.Internal.oracle (F := F) g₁ X₁ (Sum.inr m)).run (projCK ρh qS k s)
      = (BLS.ROM.Internal.getDlogS (F := F) m).run ((projCK ρh qS k s).1, insert m (projCK ρh qS k s).2)
          >>= fun v => pure (v.1 • X₁, v.2) := by
    simp only [BLS.ROM.Internal.oracle, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
  rw [hL, hR, getDlogS_run, getDlogS_run,
    show ((projCK ρh qS k s).1, insert m (projCK ρh qS k s).2).1 m
        = (s.1 m).map (fun ρ => ρ + (if k m = 0 then ρh else 0)) from rfl]
  cases hsm : s.1 m with
  | some ρ => simp only [Option.map_some, pure_bind, hval, projCK]
  | none =>
      simp only [Option.map_none, bind_assoc, pure_bind, hval, projCK_update]
      exact evalSPMF_ext (probOutput_bind_add_right_uniform F (if k m = 0 then ρh else 0)
        (fun v => pure (v • X₁, (Function.update (projCK ρh qS k s).1 m (some v), insert m s.2))))

omit [Fintype M] [Fintype F] [DecidableEq G₁] in
/-- **Coupling A′ (eager, per fixed `k`).**  Projected by `projCK`, the whole `realCoronK k` simulation
is distributionally the real BLS simulation on the projected state — for *every* adversary and every
fixed coin function `k`. -/
theorem coupling_A'_K (g₁ X₁ h xh : G₁) (ρh : F) (qS : ℕ) (k : M → Fin (qS + 1))
    (hh : h = ρh • g₁) (hxh : xh = ρh • X₁) {α : Type}
    (adv : OracleComp (advSpec M G₁) α) :
    ∀ s : (M → Option F) × Finset M,
      𝒮[(simulateQ (realCoronK (F := F) g₁ X₁ h xh qS k) adv).run s
          >>= fun z => pure (z.1, projCK ρh qS k z.2)]
        = 𝒮[(simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ X₁) adv).run (projCK ρh qS k s)] := by
  induction adv using OracleComp.inductionOn with
  | pure a => intro s; simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind q k' ih =>
      intro s
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      refine evalSPMF_bind_proj_congr (projCK ρh qS k)
        ((realCoronK (F := F) g₁ X₁ h xh qS k q).run s)
        ((BLS.ROM.Internal.oracle (F := F) g₁ X₁ q).run (projCK ρh qS k s))
        (fun b t => (simulateQ (realCoronK (F := F) g₁ X₁ h xh qS k) (k' b)).run t)
        (fun b t => (simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ X₁) (k' b)).run t)
        ?_ (fun b t => ih b t)
      rcases q with (n | m) | m
      · exact realCoronK_step_proj_unif g₁ X₁ h xh ρh qS k n s
      · exact realCoronK_step_proj_inl g₁ X₁ h xh ρh qS k m hh s
      · exact realCoronK_step_proj_inr g₁ X₁ h xh ρh qS k m hxh s

/-! ## The coin-partitioning probability (ported from the Aristotle-proved kernel) -/

/-- **Coin counting** (Aristotle-proved, Mathlib-only): the number of coin functions with `f m* = 0`
and `f s ≠ 0` for all `s ∈ S` is `qS^{|S|}·(qS+1)^{|M|−|S|−1}`. -/
theorem coin_partition_card (qS : ℕ) (S : Finset M) (mstar : M) (hm : mstar ∉ S) :
    (Finset.univ.filter (fun f : M → Fin (qS + 1) => f mstar = 0 ∧ ∀ s ∈ S, f s ≠ 0)).card
      = qS ^ S.card * (qS + 1) ^ (Fintype.card M - S.card - 1) := by
  classical
  set t : M → Finset (Fin (qS + 1)) := fun m =>
    if m = mstar then {0} else if m ∈ S then Finset.univ \ {0} else Finset.univ with ht
  have hset : (Finset.univ.filter (fun f : M → Fin (qS + 1) => f mstar = 0 ∧ ∀ s ∈ S, f s ≠ 0))
      = Fintype.piFinset t := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, ht]
    constructor
    · rintro ⟨h0, hS⟩ m
      by_cases hmstar : m = mstar
      · simp [hmstar, h0]
      · by_cases hmS : m ∈ S
        · simp [hmstar, hmS, hS m hmS]
        · simp [hmstar, hmS]
    · intro h
      refine ⟨by have := h mstar; simpa using this, ?_⟩
      intro s hs
      have := h s
      have hsne : s ≠ mstar := by rintro rfl; exact hm hs
      simp [hsne, hs] at this
      exact this
  rw [hset, Fintype.card_piFinset]
  have hcard : ∀ m, (t m).card = if m = mstar then 1 else if m ∈ S then qS else qS + 1 := by
    intro m
    simp only [ht]
    by_cases h1 : m = mstar
    · simp [h1]
    · by_cases h2 : m ∈ S
      · simp only [h1, if_false, h2, if_true]
        rw [Finset.card_sdiff]; simp
      · simp [h1, h2]
  simp only [hcard]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ mstar)]
  rw [if_pos rfl, one_mul]
  have herase : ∀ m ∈ Finset.univ.erase mstar,
      (if m = mstar then 1 else if m ∈ S then qS else qS + 1) = (if m ∈ S then qS else qS + 1) := by
    intro m hmem
    rw [if_neg (Finset.ne_of_mem_erase hmem)]
  rw [Finset.prod_congr rfl herase, Finset.prod_ite]
  have hf1 : (Finset.univ.erase mstar).filter (fun x => x ∈ S) = S := by
    ext x; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => h.2, fun hx => ⟨fun h => hm (h ▸ hx), hx⟩⟩
  simp only [Finset.prod_const, hf1]
  have hneg : ((Finset.univ.erase mstar).filter (fun x => ¬ x ∈ S)).card
      = Fintype.card M - S.card - 1 := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.erase mstar) (fun x => x ∈ S)
    rw [hf1] at hsum
    rw [Finset.card_erase_of_mem (Finset.mem_univ mstar), Finset.card_univ] at hsum
    omega
  rw [hneg]

open scoped ENNReal in
/-- **Coin probability** in the VCVio uniform-sampling setting: over a uniform coin function, the
"forgery drew `c = 1`, every signed message drew `c = 0`" event has probability `δ(1−δ)^{|S|}`,
`δ = (qS+1)⁻¹`. -/
lemma coin_prob_eq (qS : ℕ) (S : Finset M) (mstar : M) (hm : mstar ∉ S) :
    Pr[fun k : M → Fin (qS + 1) => k mstar = 0 ∧ ∀ s ∈ S, k s ≠ 0 | $ᵗ (M → Fin (qS + 1))]
      = (qS + 1 : ℝ≥0∞)⁻¹ * ((qS : ℝ≥0∞) / (qS + 1)) ^ S.card := by
  classical
  rw [probEvent_uniformSample, coin_partition_card qS S mstar hm, Fintype.card_fun,
    Fintype.card_fin]
  have hk : S.card + 1 ≤ Fintype.card M := by
    have hlt : S.card < Fintype.card M := by
      rw [← Finset.card_univ]
      exact Finset.card_lt_card ⟨Finset.subset_univ S, fun h => hm (h (Finset.mem_univ mstar))⟩
    omega
  set n := Fintype.card M
  set c := S.card
  have ha0 : (qS + 1 : ℝ≥0∞) ≠ 0 := by positivity
  have hatop : (qS + 1 : ℝ≥0∞) ≠ ⊤ := by simp
  push_cast
  set a : ℝ≥0∞ := (qS : ℝ≥0∞) + 1 with hadef
  have he : a ^ n = a ^ (n - c - 1) * a ^ (c + 1) := by rw [← pow_add]; congr 1; omega
  rw [he, mul_comm ((qS : ℝ≥0∞) ^ c) (a ^ (n - c - 1))]
  rw [ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ ha0) (ENNReal.pow_ne_top hatop)]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow, ENNReal.inv_pow, pow_succ]
  ring

/-! ## Assembly of the `q_S` bound -/

/-- Real BLS acceptance predicate on a run outcome: `m*` was hash-queried (cached), the forgery
verifies, and `m*` is fresh.  The cachedness conjunct makes forgeries *extractable* (an uncached `m*`
has `H(m*) = 0`, unusable); `hq` below shows it is free (WLOG the adversary hashes `m*`). -/
def accR (g₁ : G₁) (g₂ : G₂) (x : F)
    (out : (M × G₁) × ((M → Option F) × Finset M)) : Prop :=
  (out.2.1 out.1.1).isSome = true
    ∧ pairing (F := F) (Gₜ := Gₜ) out.1.2 g₂
        = pairing (F := F) (Gₜ := Gₜ) (((out.2.1 out.1.1).getD 0) • g₁) (x • g₂)
    ∧ out.1.1 ∉ out.2.2

/-- The winning coin event on a run outcome: the forgery message drew `c = 1` (`k m* = 0`) and every
signed message drew `c = 0` (`k s ≠ 0`). -/
def coinE (qS : ℕ) (k : M → Fin (qS + 1))
    (out : (M × G₁) × ((M → Option F) × Finset M)) : Prop :=
  k out.1.1 = 0 ∧ ∀ s ∈ out.2.2, k s ≠ 0

omit [Fintype F] [DecidableEq G₁] in
open scoped ENNReal in
/-- **Coin factor.**  For the real run, averaging the winning coin event over a uniform coin function
loses only the factor `δ(1−δ)^{q_S}`: the coins are independent of the run, and on an accepting outcome
`m* ∉ signed`, so `coin_prob_eq` gives `δ(1−δ)^{|signed|} ≥ δ(1−δ)^{q_S}` (using `|signed| ≤ q_S`). -/
lemma coin_factor_run (qS : ℕ) (g₁ : G₁) (g₂ : G₂) (x : F) (adv : CoronAdv M G₁)
    (hqs : ∀ out ∈ support ((simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁)) adv).run ((fun _ => none), ∅)),
        out.2.2.card ≤ qS) :
    ((qS + 1 : ℝ≥0∞)⁻¹ * ((qS : ℝ≥0∞) / (qS + 1)) ^ qS)
        * Pr[accR (Gₜ := Gₜ) g₁ g₂ x
              | (simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁)) adv).run ((fun _ => none), ∅)]
      ≤ ∑' k : M → Fin (qS + 1), Pr[= k | $ᵗ (M → Fin (qS + 1))]
          * Pr[fun out => accR (Gₜ := Gₜ) g₁ g₂ x out ∧ coinE qS k out
                | (simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁)) adv).run ((fun _ => none), ∅)] := by
  classical
  set run := (simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁)) adv).run ((fun _ => none), ∅) with hrun
  set c := (qS + 1 : ℝ≥0∞)⁻¹ * ((qS : ℝ≥0∞) / (qS + 1)) ^ qS with hc
  have hR : (∑' k : M → Fin (qS + 1), Pr[= k | $ᵗ (M → Fin (qS + 1))]
        * Pr[fun out => accR (Gₜ := Gₜ) g₁ g₂ x out ∧ coinE qS k out | run])
      = ∑' out, (if accR (Gₜ := Gₜ) g₁ g₂ x out
          then Pr[= out | run] * Pr[fun k => coinE qS k out | $ᵗ (M → Fin (qS + 1))] else 0) := by
    simp_rw [probEvent_eq_tsum_ite run, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun out => ?_
    by_cases hacc : accR (Gₜ := Gₜ) g₁ g₂ x out
    · simp only [hacc, true_and, if_true]
      rw [probEvent_eq_tsum_ite ($ᵗ (M → Fin (qS + 1))) (fun k => coinE qS k out),
        ← ENNReal.tsum_mul_left]
      refine tsum_congr fun k => ?_
      by_cases hck : coinE qS k out <;> simp [hck, mul_comm]
    · simp only [hacc, false_and, if_false, mul_zero, tsum_zero]
  rw [hR, probEvent_eq_tsum_ite run (accR (Gₜ := Gₜ) g₁ g₂ x), ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun out => ?_
  rw [mul_ite, mul_zero]
  by_cases hacc : accR (Gₜ := Gₜ) g₁ g₂ x out
  · simp only [hacc, if_true]
    by_cases hsupp : out ∈ support run
    · have hmem : out.1.1 ∉ out.2.2 := hacc.2.2
      simp only [coinE]
      rw [coin_prob_eq qS out.2.2 out.1.1 hmem, mul_comm (Pr[= out | run])]
      refine mul_le_mul_left ?_ _
      rw [hc]
      refine mul_le_mul_right (pow_le_pow_right_of_le_one' ?_ (hqs out hsupp)) _
      calc (qS : ℝ≥0∞) / (qS + 1) ≤ (qS + 1) / (qS + 1) := by
            gcongr
            simp
        _ = 1 := ENNReal.div_self (by positivity) (by simp)
    · simp only [probOutput_eq_zero_of_not_mem_support hsupp, mul_zero, zero_mul, le_refl]
  · simp only [hacc, if_false, le_refl]

omit [Fintype M] [DecidableEq M] [SampleableType F] [Fintype F] in
/-- The empty state projects to itself. -/
lemma projCK_empty (ρh : F) (qS : ℕ) (k : M → Fin (qS + 1)) :
    projCK ρh qS k ((fun _ => none), ∅) = ((fun _ => none), ∅) := by
  refine Prod.ext ?_ rfl; funext m; simp [projCK]

omit [Fintype M] [Fintype F] [DecidableEq G₁] in
/-- **Reduction lower bound (per fixed `x`, `ρ_h`, `k`).**  The accepting-and-winning-coins event on the
real run is bounded by the reduction's success (its output equals `x·h`).  Chains: coupling A′-K (move
to the `realCoronK` run projected by `projCK`), coupling B′-K (move to the `coronOracleK` run off the
abort event, which the winning coins forbid), and `coron_extract` (a verifying forgery on a `c=1`
challenge message yields `x·h`). -/
lemma reduction_lb (g₁ : G₁) (g₂ : G₂) (x ρh : F) (qS : ℕ) (k : M → Fin (qS + 1))
    (adv : CoronAdv M G₁)
    (hinj : Function.Injective (fun z : G₁ => pairing (F := F) (Gₜ := Gₜ) z g₂)) :
    Pr[fun out => accR (Gₜ := Gₜ) g₁ g₂ x out ∧ coinE qS k out
        | (simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁)) adv).run ((fun _ => none), ∅)]
      ≤ Pr[fun z => z.1.2 - (((z.2.1 z.1.1).getD 0) • (x • g₁)) = x • (ρh • g₁)
        | (simulateQ (coronOracleK (F := F) g₁ (x • g₁) (ρh • g₁) qS k) adv).run ((fun _ => none), ∅)] := by
  classical
  -- move the real run to the projected `realCoronK` run (coupling A′-K)
  have hd := coupling_A'_K g₁ (x • g₁) (ρh • g₁) (ρh • (x • g₁)) ρh qS k rfl rfl adv
    ((fun _ => none), ∅)
  rw [projCK_empty] at hd
  have hA : Pr[fun out => accR (Gₜ := Gₜ) g₁ g₂ x out ∧ coinE qS k out
        | (simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁)) adv).run ((fun _ => none), ∅)]
      = Pr[fun z => accR (Gₜ := Gₜ) g₁ g₂ x (z.1, projCK ρh qS k z.2)
              ∧ coinE qS k (z.1, projCK ρh qS k z.2)
        | (simulateQ (realCoronK (F := F) g₁ (x • g₁) (ρh • g₁) (ρh • (x • g₁)) qS k) adv).run
            ((fun _ => none), ∅)] := by
    rw [show Pr[fun out => accR (Gₜ := Gₜ) g₁ g₂ x out ∧ coinE qS k out
        | (simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁)) adv).run ((fun _ => none), ∅)]
      = Pr[fun out => accR (Gₜ := Gₜ) g₁ g₂ x out ∧ coinE qS k out
        | (simulateQ (realCoronK (F := F) g₁ (x • g₁) (ρh • g₁) (ρh • (x • g₁)) qS k) adv).run
            ((fun _ => none), ∅) >>= fun z => pure (z.1, projCK ρh qS k z.2)]
      from by rw [probEvent_def, probEvent_def, hd]]
    rw [probEvent_bind_eq_tsum]
    simp only [probEvent_pure, mul_ite, mul_one, mul_zero]
    rw [← probEvent_eq_tsum_ite]
  rw [hA, ← coupling_coron_realCoron_K_gen g₁ (x • g₁) (ρh • g₁) (ρh • (x • g₁)) qS k adv
      (fun z => accR (Gₜ := Gₜ) g₁ g₂ x (z.1, projCK ρh qS k z.2) ∧ coinE qS k (z.1, projCK ρh qS k z.2))
      (by rintro z ⟨-, hcoin⟩ ⟨m, hmem, hk0⟩; exact hcoin.2 m hmem hk0)]
  -- extraction: a verifying `c = 1` forgery yields `x·h`
  refine probEvent_mono (fun z _ hQ => ?_)
  obtain ⟨⟨hsome, hpair, _hfresh⟩, hk0, _⟩ := hQ
  simp only [projCK, hk0, if_true] at hsome hpair
  cases hzc : z.2.1 z.1.1 with
  | none => rw [hzc] at hsome; simp at hsome
  | some ρc =>
      rw [hzc] at hpair
      simp only [Option.map_some, Option.getD_some] at hpair
      have hver : pairing (F := F) (Gₜ := Gₜ) z.1.2 g₂
          = pairing (F := F) (Gₜ := Gₜ) (ρc • g₁ + ρh • g₁) (x • g₂) := by
        rw [hpair, add_smul]
      have hextr := coron_extract (Gₜ := Gₜ) g₁ g₂ x ρc (ρh • g₁) z.1.2 (x • g₁) rfl hinj hver
      simp only [Option.getD_some]
      exact hextr

omit [Fintype F] [DecidableEq G₁] in
open scoped ENNReal in
/-- **Per-`x` bound.**  For fixed secret `x`, the coin factor (`coin_factor_run`) plus the reduction
lower bound (`reduction_lb`), averaged over the challenge dlog `ρ_h` and coin function `k`. -/
lemma per_x (g₁ : G₁) (g₂ : G₂) (x : F) (qS : ℕ) (adv : CoronAdv M G₁)
    (hinj : Function.Injective (fun z : G₁ => pairing (F := F) (Gₜ := Gₜ) z g₂))
    (hqs : ∀ out ∈ support ((simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁)) adv).run ((fun _ => none), ∅)),
        out.2.2.card ≤ qS) :
    ((qS + 1 : ℝ≥0∞)⁻¹ * ((qS : ℝ≥0∞) / (qS + 1)) ^ qS)
        * Pr[accR (Gₜ := Gₜ) g₁ g₂ x
              | (simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁)) adv).run ((fun _ => none), ∅)]
      ≤ ∑' ρh : F, Pr[= ρh | $ᵗ F] * ∑' k : M → Fin (qS + 1), Pr[= k | $ᵗ (M → Fin (qS + 1))]
          * Pr[fun z => z.1.2 - (((z.2.1 z.1.1).getD 0) • (x • g₁)) = x • (ρh • g₁)
            | (simulateQ (coronOracleK (F := F) g₁ (x • g₁) (ρh • g₁) qS k) adv).run
                ((fun _ => none), ∅)] := by
  have h1 := coin_factor_run (Gₜ := Gₜ) qS g₁ g₂ x adv hqs
  have hsum1 : ∑' ρh : F, Pr[= ρh | $ᵗ F]
      * (((qS + 1 : ℝ≥0∞)⁻¹ * ((qS : ℝ≥0∞) / (qS + 1)) ^ qS)
          * Pr[accR (Gₜ := Gₜ) g₁ g₂ x
                | (simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁)) adv).run ((fun _ => none), ∅)])
      = ((qS + 1 : ℝ≥0∞)⁻¹ * ((qS : ℝ≥0∞) / (qS + 1)) ^ qS)
          * Pr[accR (Gₜ := Gₜ) g₁ g₂ x
                | (simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁)) adv).run ((fun _ => none), ∅)] := by
    rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_sub, probFailure_uniformSample, tsub_zero, one_mul]
  rw [← hsum1]
  refine ENNReal.tsum_le_tsum fun ρh => mul_le_mul_right (le_trans h1 ?_) _
  exact ENNReal.tsum_le_tsum fun k =>
    mul_le_mul_right (reduction_lb (Gₜ := Gₜ) g₁ g₂ x ρh qS k adv hinj) _

omit [Fintype F] in
open scoped ENNReal in
/-- **Public-key-aware BLS EUF-CMA ⇒ co-CDH — the `~e·q_S` (Coron) bound.**
This is the full Coron theorem: after `x` is sampled, the adversary is instantiated with the public
key `x·g₂`; the co-CDH reduction uses its input `X₂` to instantiate the same adversary family.
The reduction in the conclusion samples and caches its hidden coin only on the first query to each
message; the full table used below is solely a distributionally equivalent counting game. -/
theorem bls_eufcma_le_cocdh_coron_pk [SampleableType G₁] [Fintype G₁] [DecidableEq Gₜ]
    (g₁ : G₁) (g₂ : G₂) (qS : ℕ) (adv : CoronAdvPK M G₁ G₂)
    (hgenbij : Function.Bijective (fun r : F => r • g₁))
    (hinj : Function.Injective (fun z : G₁ => pairing (F := F) (Gₜ := Gₜ) z g₂))
    (hqs : ∀ x : F, ∀ out ∈ support
        ((simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁)) (adv (x • g₂))).run
          ((fun _ => none), ∅)),
        out.2.2.card ≤ qS)
    (hq : ∀ x : F, ∀ out ∈ support
        ((simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁)) (adv (x • g₂))).run
          ((fun _ => none), ∅)),
        (pairing (F := F) (Gₜ := Gₜ) out.1.2 g₂
              = pairing (F := F) (Gₜ := Gₜ) (((out.2.1 out.1.1).getD 0) • g₁) (x • g₂)
            ∧ out.1.1 ∉ out.2.2) → (out.2.1 out.1.1).isSome = true) :
    Pr[= true | blsEufTightPK (F := F) (Gₜ := Gₜ) g₁ g₂ adv]
      ≤ ((qS + 1 : ℝ≥0∞)⁻¹ * ((qS : ℝ≥0∞) / (qS + 1)) ^ qS)⁻¹
          * Pr[= true | coCDHExp (F := F) g₁ g₂ (coronReductionLazyPK qS adv)] := by
  classical
  have hlazy :
      Pr[= true | coCDHExp (F := F) g₁ g₂ (coronReductionLazyPK qS adv)] =
        Pr[= true | coCDHExp (F := F) g₁ g₂ (coronReductionKPK qS adv)] :=
    probOutput_congr rfl (coCDHExp_coronReductionLazyPK_evalSPMF g₁ g₂ qS adv)
  set c := (qS + 1 : ℝ≥0∞)⁻¹ * ((qS : ℝ≥0∞) / (qS + 1)) ^ qS with hcdef
  have hctop : c ≠ ⊤ := by
    rw [hcdef]; apply ENNReal.mul_ne_top; · simp
    · exact ENNReal.pow_ne_top (by simp [ENNReal.div_eq_top])
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    refine mul_ne_zero (by simp) ?_
    rcases Nat.eq_zero_or_pos qS with h | h
    · simp [h]
    · refine pow_ne_zero _ ?_
      rw [Ne, ENNReal.div_eq_zero_iff, not_or]
      exact ⟨by exact_mod_cast h.ne', by simp⟩
  have ha : Pr[= true | blsEufTightPK (F := F) (Gₜ := Gₜ) g₁ g₂ adv]
      = ∑' x : F, Pr[= x | $ᵗ F] * Pr[accR (Gₜ := Gₜ) g₁ g₂ x
          | (simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁)) (adv (x • g₂))).run
              ((fun _ => none), ∅)] := by
    simp only [blsEufTightPK]
    rw [probOutput_bind_eq_tsum]
    refine tsum_congr fun x => ?_
    congr 1
    simp only [← Bool.decide_and]
    rw [bind_pure_comp, probOutput_map]
    simp only [decide_eq_true_eq]
    refine le_antisymm (probEvent_mono fun out hout hAB => ⟨hq x out hout hAB, hAB.1, hAB.2⟩)
      (probEvent_mono fun out _ h => ⟨h.2.1, h.2.2⟩)
  have hb : Pr[= true | coCDHExp (F := F) g₁ g₂ (coronReductionKPK qS adv)]
      = ∑' x : F, Pr[= x | $ᵗ F] * ∑' ρh : F, Pr[= ρh | $ᵗ F]
          * ∑' k : M → Fin (qS + 1), Pr[= k | $ᵗ (M → Fin (qS + 1))]
          * Pr[fun z => z.1.2 - (((z.2.1 z.1.1).getD 0) • (x • g₁)) = x • (ρh • g₁)
            | (simulateQ (coronOracleK (F := F) g₁ (x • g₁) (ρh • g₁) qS k)
                (adv (x • g₂))).run ((fun _ => none), ∅)] := by
    simp only [coCDHExp, coronReductionKPK, bind_assoc, pure_bind]
    rw [probOutput_bind_eq_tsum]
    refine tsum_congr fun x => ?_
    congr 1
    rw [probOutput_congr rfl
      (evalSPMF_bind_bijective_add_right_uniform (α := F) (β := G₁) (· • g₁) hgenbij 0 _).symm]
    simp only [add_zero]
    rw [probOutput_bind_eq_tsum]
    refine tsum_congr fun ρh => ?_
    congr 1
    rw [probOutput_bind_eq_tsum]
    refine tsum_congr fun k => ?_
    congr 1
    rw [bind_pure_comp, probOutput_map]
    simp only [decide_eq_true_eq]
  have hcore : c * Pr[= true | blsEufTightPK (F := F) (Gₜ := Gₜ) g₁ g₂ adv]
      ≤ Pr[= true | coCDHExp (F := F) g₁ g₂ (coronReductionKPK qS adv)] := by
    rw [ha, hb, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun x => ?_
    rw [← mul_assoc, mul_comm c (Pr[= x | $ᵗ F]), mul_assoc]
    exact mul_le_mul_right
      (per_x (Gₜ := Gₜ) g₁ g₂ x qS (adv (x • g₂)) hinj (hqs x)) _
  calc Pr[= true | blsEufTightPK (F := F) (Gₜ := Gₜ) g₁ g₂ adv]
      = c⁻¹ * (c * Pr[= true | blsEufTightPK (F := F) (Gₜ := Gₜ) g₁ g₂ adv]) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
    _ ≤ c⁻¹ * Pr[= true | coCDHExp (F := F) g₁ g₂ (coronReductionKPK qS adv)] := by
        exact mul_le_mul_right hcore _
    _ = c⁻¹ * Pr[= true | coCDHExp (F := F) g₁ g₂ (coronReductionLazyPK qS adv)] := by
        rw [hlazy]

omit [Fintype F] in
open scoped ENNReal in
/-- **Direct pk-aware lazy-ROM BLS EUF-CMA ⇒ co-CDH.**

The adversary interacts with hash and signing oracles.  Verification appends one on-demand hash
query for the forgery message, so cachedness is derived rather than assumed.  `hqs` bounds the
number of distinct messages recorded by the signing oracle; hash queries are unrestricted.  The
co-CDH reduction on the right also samples dlogs and hidden Coron coins on demand. -/
theorem bls_eufcma_le_cocdh_coron_lazy_pk [SampleableType G₁] [Fintype G₁] [DecidableEq Gₜ]
    (g₁ : G₁) (g₂ : G₂) (qS : ℕ) (adv : AdversaryPK M G₁ G₂)
    (hgenbij : Function.Bijective (fun r : F => r • g₁))
    (hinj : Function.Injective (fun z : G₁ => pairing (F := F) (Gₜ := Gₜ) z g₂))
    (hqs : ∀ x : F, ∀ out ∈ support
        ((simulateQ (BLS.ROM.Internal.oracle (F := F) g₁ (x • g₁)) (adv (x • g₂))).run
          ((fun _ => none), ∅)),
        out.2.2.card ≤ qS) :
    Pr[= true | blsEufLazyPK (F := F) (Gₜ := Gₜ) g₁ g₂ adv]
      ≤ ((qS + 1 : ℝ≥0∞)⁻¹ * ((qS : ℝ≥0∞) / (qS + 1)) ^ qS)⁻¹
          * Pr[= true | coCDHExp (F := F) g₁ g₂
              (coronReductionLazyPK qS (cacheForgeryPK adv))] := by
  unfold blsEufLazyPK
  refine bls_eufcma_le_cocdh_coron_pk g₁ g₂ qS (cacheForgeryPK adv) hgenbij hinj
    (fun x out hout => ?_) (fun x out hout _ => ?_)
  · exact (cacheForgery_run_support g₁ (x • g₁) (adv (x • g₂)) qS (hqs x) out
      (by simpa only [cacheForgeryPK] using hout)).1
  · exact (cacheForgery_run_support g₁ (x • g₁) (adv (x • g₂)) qS (hqs x) out
      (by simpa only [cacheForgeryPK] using hout)).2

end BLS.CoCDH.Coron
