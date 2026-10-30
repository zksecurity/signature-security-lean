import Signatures.SynchronizedPS.Spec.Reduction
import Proofs.SynchronizedPS.Adaptive
import Proofs.LinearFunctional.LazyAGM
import Proofs.BLS.LazyAGMReduction
import Proofs.Model.DirectAGM

/-! The synchronized PS coefficient game, coupled to the two-secret adaptive core. The attacker's
proof view runs against the shared lazy base oracle; replacing the oracle by a uniform table and
the table by programmed scalars gives the core's real game, and the three explicit solvers are the
core's reductions at the weights `wᵢ(t, m) = [i = t]`, `s(t, m) = m`. Periods are finite here. -/

open BilinearGroup OracleComp OracleSpec AlgebraicGroupModel AlgebraicGroupModel.LinFunctional
open Model Model.LazyAGM Model.LazyAGM.Proofs
open BLS.LazyAGM.Reduction (table_random table_lookup)

namespace SynchronizedPS.Proofs

variable {F Period G₁ G₂ Gₜ : Type}
  [Field F] [SampleableType F] [Fintype F] [DecidableEq F] [Fintype Period] [DecidableEq Period]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

/-- Weight of base `i` in the hash of `(t, m)`: one at `i = t`. -/
def weight (i : Period) (m : Period × F) : F := if i = m.1 then 1 else 0

/-- The message scalar. -/
abbrev scalar : Period × F → F := Prod.snd

omit [SampleableType F] [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] in
theorem muW_weight (ρ : Period → F) (m : Period × F) : muW weight ρ m = ρ m.1 := by
  simp [muW, weight]

omit [SampleableType F] [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] in
theorem sum_weight_smul (H : Period → G₁) (m : Period × F) : ∑ i, weight i m • H i = H m.1 := by
  simp [weight, ite_smul]

/-- A grouped proof view of a synchronized PS attacker: one oracle program per key pair, reporting
a forgery with its coefficients. The proof-side games and solvers use the attacker only through
such a view, so they transport along period relabelings. -/
abbrev View (F Period G₁ G₂ : Type) : Type :=
  DirectAGM.ProofView.View F Period (Period × F) (Forgery F Period) G₁ (G₂ × G₂)

/-- The attacker's grouped proof view from `g₁` and the key's two components. -/
abbrev view (adversary : Reduction.Adversary F Period G₁ G₂) (g₁ : G₁) : View F Period G₁ G₂ :=
  DirectAGM.ProofView.adversaryWith g₁ (fun pk : G₂ × G₂ => [pk.1, pk.2]) adversary

/-- `Reduction.run` on a view: fixed hash and signing tables, with transcripts. -/
def runV (V : View F Period G₁ G₂) (publicKey : G₂ × G₂) (hash : Period → G₁) (sign : Period × F → G₁) :
    ProbComp (Output F (Forgery F Period) × Transcript Period (Period × F) G₁) :=
  (simulateQ (fixedImpl hash sign) (V.main publicKey)).run ([], [])

theorem run_eq_runV (adversary : Reduction.Adversary F Period G₁ G₂) (g₁ : G₁) (publicKey : G₂ × G₂)
    (hash : Period → G₁) (sign : Period × F → G₁) :
    Reduction.run adversary g₁ publicKey hash sign = runV (view adversary g₁) publicKey hash sign := rfl

/-! ## The coefficient game on the shared lazy base oracle -/

def signing (x y : F) (m : Period × F) : OracleComp (baseSpec Period G₁) G₁ := do
  let H ← (liftM ((baseSpec Period G₁).query (.inr m.1)) : OracleComp (baseSpec Period G₁) G₁)
  pure ((x + y * m.2) • H)

def lazyRun (V : View F Period G₁ G₂) (x y : F) (pk : G₂ × G₂) :
    OracleComp (baseSpec Period G₁) (Output F (Forgery F Period) × Transcript Period (Period × F) G₁) :=
  (simulateQ (handler
    (fun n => (liftM ((baseSpec Period G₁).query (.inl n)) : OracleComp (baseSpec Period G₁) _))
    (fun i => (liftM ((baseSpec Period G₁).query (.inr i)) : OracleComp (baseSpec Period G₁) G₁))
    (signing x y)) (V.main pk)).run ([], [])

/-- The readable game's checks on the attacker's report: a fresh period/message, one honest
signature per period, and the pairing equation of the hash of the attacked period against the
honest key and the message. -/
def accepts (g₂ : G₂) (x y : F) (data : Forgery F Period) (aggregate : G₁)
    (signed : List (Period × F)) (hash : G₁) : Bool :=
  decide (data ∉ signed ∧ onePerPeriod data signed) &&
  decide (pairing (F := F) (Gₜ := Gₜ) hash (x • g₂ + data.2 • (y • g₂)) =
    pairing (F := F) (Gₜ := Gₜ) aggregate g₂)

/-- The group element the attacker's coefficients name. -/
def aggregate (g₁ : G₁) (out : Output F (Forgery F Period)) (tr : Transcript Period (Period × F) G₁) : G₁ :=
  out.β • g₁ + weightedReplies out.γ tr.1 + weightedReplies out.ξ tr.2

noncomputable def experiment (g₁ : G₁) (g₂ : G₂) (V : View F Period G₁ G₂) :
    OracleComp (baseSpec Period G₁) Bool := do
  let x ← (liftM ($ᵗ F) : OracleComp (baseSpec Period G₁) F)
  let y ← (liftM ($ᵗ F) : OracleComp (baseSpec Period G₁) F)
  let (out, tr) ← lazyRun V x y (x • g₂, y • g₂)
  let hash ← (liftM ((baseSpec Period G₁).query (.inr out.mstar.1)) : OracleComp (baseSpec Period G₁) G₁)
  pure (accepts (Gₜ := Gₜ) g₂ x y out.mstar (aggregate g₁ out tr) (tr.2.map Prod.fst) hash)

noncomputable def lazyGame (g₁ : G₁) (g₂ : G₂) (V : View F Period G₁ G₂) :
    ProbComp Bool :=
  (simulateQ lazyImpl (experiment (Gₜ := Gₜ) g₁ g₂ V)).run' ∅

/-! ## Fixing the base table -/

omit [SampleableType F] [Fintype F] [DecidableEq F] [Fintype Period] [DecidableEq Period]
  [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]
  [DecidableEq Gₜ] in
theorem lazyRun_table (V : View F Period G₁ G₂) (x y : F) (pk : G₂ × G₂) (H : Period → G₁) :
    simulateQ (BLS.CoCDH.coinTableImpl H) (lazyRun V x y pk) =
      runV V pk H (fun m => (x + y * m.2) • H m.1) := by
  unfold lazyRun runV
  apply simulateQ_StateT_compose
  intro q tr
  rcases q with (n | i) | m <;>
    simp only [handler, fixedImpl, StateT.run, StateT.mk, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, signing, pure_bind, table_random, table_lookup]

omit [Fintype F] [Fintype Period] [SampleableType G₁] [Fintype G₁] in
theorem experiment_table (g₁ : G₁) (g₂ : G₂) (V : View F Period G₁ G₂) (H : Period → G₁) :
    simulateQ (BLS.CoCDH.coinTableImpl H) (experiment (Gₜ := Gₜ) g₁ g₂ V) = (do
      let x ← ($ᵗ F : ProbComp F)
      let y ← ($ᵗ F : ProbComp F)
      let (out, tr) ← runV V (x • g₂, y • g₂) H (fun m => (x + y * m.2) • H m.1)
      pure (accepts (Gₜ := Gₜ) g₂ x y out.mstar (aggregate g₁ out tr) (tr.2.map Prod.fst)
        (H out.mstar.1))) := by
  simp only [experiment, simulateQ_bind, simulateQ_pure, lazyRun_table, simulateQ_spec_query,
    table_lookup, pure_bind]
  simp [BLS.CoCDH.coinTableImpl, QueryImpl.simulateQ_add_liftM_left]

/-! ## The core's real game -/

/-- The game's admissibility rule on the exact signing transcript. -/
def valid (fo : DynForgery F (Period × F) Period) : Prop :=
  onePerPeriod fo.2.mstar (List.ofFn fo.2.v)

def project (out : Output F (Forgery F Period)) : Output F (Period × F) :=
  ⟨out.mstar, out.β, out.γ, out.ξ⟩

/-- The core's offset forgery, with no co-signer offset. -/
def toOffsetForgery (z : Output F (Forgery F Period) × Transcript Period (Period × F) G₁) :
    OffsetForgery F (Period × F) Period :=
  ⟨toForgery (project z.1, z.2), 0⟩

/-- The attacker as the core's representation producer. -/
def extracted (V : View F Period G₁ G₂) : AdaptiveAdv F (Period × F) Period G₁ G₂ :=
  fun pk H signO => toOffsetForgery <$> runV V pk H signO

omit [SampleableType F] [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] in
theorem realSign_weight (x y : F) (H : Period → G₁) :
    realSign weight scalar x y H = fun m => (x + y * m.2) • H m.1 := by
  funext m
  simp only [realSign, LinFunctional.realSign, sum_weight_smul, scalar]

omit [SampleableType F] [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [DecidableEq Gₜ] in
theorem verification_iff (g₁ : G₁) (g₂ : G₂) (x y : F) (out : Output F (Forgery F Period))
    (tr : Transcript Period (Period × F) G₁) (H : Period → G₁)
    (signO : Period × F → G₁) (hc : Consistent H signO (project out, tr).2) :
    pairing (F := F) (Gₜ := Gₜ) (H out.mstar.1) (x • g₂ + out.mstar.2 • (y • g₂)) =
      pairing (F := F) (Gₜ := Gₜ) (aggregate g₁ out tr) g₂ ↔
      pairing (F := F) (Gₜ := Gₜ) (dynForgeryElem g₁ (toOffsetForgery (out, tr)).rep H signO) g₂ =
        pairing (F := F) (Gₜ := Gₜ) (dynTargetElem weight (toOffsetForgery (out, tr)).rep H)
          ((x + y * scalar (toOffsetForgery (out, tr)).rep.2.mstar +
            (toOffsetForgery (out, tr)).offset) • g₂) := by
  rw [aggregate, toOffsetForgery, dynTargetElem, targetElem, sum_weight_smul,
    ← materialize_eq g₁ H signO (project out, tr) hc, materialize_eq_weightedReplies, eq_comm]
  simp only [project, toForgery, smul_smul, ← add_smul, add_zero]
  rw [mul_comm out.mstar.2 y]

omit [Fintype F] in
theorem lazyGame_eq_realGame (g₁ : G₁) (g₂ : G₂) (V : View F Period G₁ G₂) :
    𝒟[lazyGame (Gₜ := Gₜ) g₁ g₂ V] {true} =
      Pr[fun z => valid z.1.rep ∧ succ (Gₜ := Gₜ) weight scalar g₁ g₂ z |
        realGame weight scalar g₂ (extracted V)] := by
  classical
  have hd := BLS.CoCDH.evalSPMF_lazyCoin_eq_table (experiment (Gₜ := Gₜ) g₁ g₂ V) ∅
  simp only [tableExtending_empty, experiment_table] at hd
  change 𝒮[lazyGame (Gₜ := Gₜ) g₁ g₂ V] = _ at hd
  rw [DeferredSampling.evalSPMF_bind_comm] at hd
  rw [evalSPMF_bind_congr' _ fun x => DeferredSampling.evalSPMF_bind_comm ($ᵗ (Period → G₁)) ($ᵗ F)
    (fun H y => do
      let (out, tr) ← runV V (x • g₂, y • g₂) H (fun m => (x + y * m.2) • H m.1)
      pure (accepts (Gₜ := Gₜ) g₂ x y out.mstar (aggregate g₁ out tr) (tr.2.map Prod.fst)
        (H out.mstar.1)))] at hd
  rw [evalDist_apply_singleton, probOutput_congr rfl hd, ← probEvent_true_eq_probOutput]
  unfold realGame extracted
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
    probEvent_bind_eq_tsum, realSign_weight]
  refine tsum_congr fun x => ?_
  congr 1
  refine tsum_congr fun y => ?_
  congr 1
  refine tsum_congr fun H => ?_
  congr 1
  refine tsum_congr fun z => ?_
  by_cases hz : z ∈ support (runV V (x • g₂, y • g₂) H (fun m => (x + y * m.2) • H m.1))
  · have hc := fixed_consistent H (fun m => (x + y * m.2) • H m.1)
      (V.main (x • g₂, y • g₂)) ([], []) (by simp [Consistent]) z hz
    congr 1
    simp only [probEvent_pure]
    apply if_congr _ rfl rfl
    obtain ⟨out, tr⟩ := z
    rw [accepts, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
      verification_iff g₁ g₂ x y out tr H _ hc]
    simp only [valid, succ, toOffsetForgery, toForgery_messages, toForgery_fresh, project]
    tauto
  · simp [probOutput_eq_zero_of_not_mem_support hz]

/-! ## Non-degeneracy: one signature per period and a fresh message -/

omit [SampleableType F] [Fintype F] [Fintype Period] [SampleableType G₁] [Fintype G₁] in
theorem nondegenerate (fo : DynForgery F (Period × F) Period) (hvalid : valid fo) (hfresh : fo.Fresh) :
    dynDenomCoeff weight fo fo.2.mstar.1 ≠ 0 ∨
      dynDenomCoeff (scaled weight scalar) fo fo.2.mstar.1 ≠ 0 := by
  obtain ⟨Q, mstar, v, β, γ, ξ⟩ := fo
  simp only [dynDenomCoeff, Lcoeff, weight, scaled, scalar, if_true, mul_ite,
    mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  by_contra h
  simp only [ne_eq, not_or, not_not] at h
  obtain ⟨h₁, h₂⟩ := h
  set S := Finset.univ.filter fun q : Fin Q => mstar.1 = (v q).1 with hS
  have hpair : ∀ a ∈ S, ∀ b ∈ S, a = b := by
    intro a ha b hb
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    have := List.pairwise_ofFn.mp hvalid
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact this hlt (ha.symm.trans hb)
    · exact this hlt (hb.symm.trans ha)
  rcases Finset.eq_empty_or_nonempty S with hempty | ⟨q₀, hq₀⟩
  · rw [hempty, Finset.sum_empty, sub_zero] at h₁
    exact one_ne_zero h₁
  · have hsingle : S = {q₀} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hq₀, fun b hb => hpair b hb q₀ hq₀⟩
    rw [hsingle, Finset.sum_singleton, sub_eq_zero] at h₁ h₂
    have hperiod : mstar.1 = (v q₀).1 := by
      simpa [hS] using hq₀
    exact hfresh q₀ (Prod.ext hperiod (by rw [← h₁, one_mul] at h₂; exact h₂))

/-! ## The explicit solvers are the core's reductions -/

section Solvers
variable (adversary : Reduction.Adversary F Period G₁ G₂) (g₁ : G₁)
  (out : Output F (Forgery F Period)) (tr : Transcript Period (Period × F) G₁) (ρ : Period → F)

omit [SampleableType F] [Fintype F] [DecidableEq F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [Fintype G₁] in
theorem baseCoeff_mul_sum (coeff : List F) (replies : List (Period × G₁)) :
    (∑ i, baseCoeff coeff replies i * ρ i) =
      (replies.mapIdx fun n p => tokenCoeff coeff n * ρ p.1).sum := by
  simp only [baseCoeff, List.mapIdx_eq_ofFn, List.sum_ofFn, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

omit [SampleableType F] [Fintype F] [DecidableEq F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [Fintype G₁] in
theorem const_eq : (dynReprA weight (toOffsetForgery (out, tr)).rep ρ).const = Reduction.const out tr ρ := by
  simp only [dynReprA, reprA, toOffsetForgery, toForgery, project, Reduction.const, baseCoeff_mul_sum]

omit [SampleableType F] [Fintype F] [DecidableEq F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [Fintype G₁] in
theorem lin_eq : (dynReprA weight (toOffsetForgery (out, tr)).rep ρ).lin = Reduction.lin out tr ρ := by
  simp only [dynReprA, reprA, toOffsetForgery, toForgery, project, Reduction.lin, muW_weight,
    List.mapIdx_eq_ofFn, List.sum_ofFn]
  rfl

omit [SampleableType F] [Fintype F] [DecidableEq F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [Fintype G₁] in
theorem lin'_eq : (dynReprA (scaled weight scalar) (toOffsetForgery (out, tr)).rep ρ).lin =
    Reduction.lin' out tr ρ := by
  simp only [dynReprA, reprA, toOffsetForgery, toForgery, project, Reduction.lin', muW_scaled,
    muW_weight, List.mapIdx_eq_ofFn, List.sum_ofFn, scalar]
  rfl

omit [SampleableType F] [Fintype F] [DecidableEq F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [Fintype G₁] in
theorem D_eq : dynDenom weight (toOffsetForgery (out, tr)).rep ρ = Reduction.D out tr ρ := by
  rw [dynDenom, dynDenomCoeff, ← muW_sub_reprA_lin, Reduction.D, ← lin_eq]
  simp only [toOffsetForgery, toForgery, project, muW_weight, dynReprA]

omit [SampleableType F] [Fintype F] [DecidableEq F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [Fintype G₁] in
theorem D'_eq : dynDenom (scaled weight scalar) (toOffsetForgery (out, tr)).rep ρ =
    Reduction.D' out tr ρ := by
  rw [dynDenom, dynDenomCoeff, ← muW_sub_reprA_lin, Reduction.D', ← lin'_eq, muW_scaled]
  simp only [toOffsetForgery, toForgery, project, muW_weight, dynReprA, scalar]

omit [SampleableType F] [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] in
theorem known_eq : known weight (toOffsetForgery (out, tr)) ρ = Reduction.K out tr ρ := by
  rw [known, Reduction.K, const_eq]
  simp only [toOffsetForgery, zero_mul, sub_zero]

omit [SampleableType F] [Fintype F] [DecidableEq F] [Fintype Period] [AddCommGroup G₁] [Module F G₁]
  [SampleableType G₁] [Fintype G₁] in
theorem reuse_eq : dynDenomCoeff weight (toOffsetForgery (out, tr)).rep out.mstar.1 =
    Reduction.reuse out tr := by
  simp only [dynDenomCoeff, Lcoeff, toOffsetForgery, toForgery, project, weight, Reduction.reuse,
    List.mapIdx_eq_ofFn, List.sum_ofFn, ite_true]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [List.get_eq_getElem]
  by_cases h : out.mstar.1 = tr.2[(q : Nat)].1.1
  · simp [h]
  · simp [h, Ne.symm h]

/-- The attacked period, the coordinate the hash-branch solver inspects. -/
def attacked (fo : DynForgery F (Period × F) Period) : Period := fo.2.mstar.1

omit [SampleableType F] [Fintype F] [SampleableType G₁] [Fintype G₁] [AddCommGroup G₁] [Module F G₁] in
theorem badDenom_eq (table : Period → F) :
    badDenom weight scalar attacked (toOffsetForgery (out, tr)).rep table =
      if Reduction.reuse out tr ≠ 0 then Reduction.D out tr table else Reduction.D' out tr table := by
  rw [badDenom, badCoeff, ← D_eq, ← D'_eq, dynDenom, dynDenom]
  have : attacked (toOffsetForgery (out, tr)).rep = out.mstar.1 := rfl
  rw [this, reuse_eq]
  split_ifs <;> rfl

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem challengeInX_eq (Z₁ : G₁) (g₂ Z₂ : G₂) :
    Reduction.challengeInX adversary g₁ Z₁ g₂ Z₂ =
      reductionX weight scalar (extracted (view adversary g₁)) g₁ Z₁ g₂ Z₂ := by
  unfold Reduction.challengeInX reductionX extracted
  apply bind_congr
  intro y
  apply bind_congr
  intro ρ
  have hsign : simSignX weight scalar g₁ Z₁ y ρ = fun m => ρ m.1 • Z₁ + (ρ m.1 * (y * m.2)) • g₁ := by
    funext m
    simp only [simSignX, muW_weight, scalar]
  rw [hsign]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply bind_congr
  rintro ⟨out, tr⟩
  simp only [guessX, known_eq, D_eq, D'_eq]

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem challengeInY_eq (Z₁ : G₁) (g₂ Z₂ : G₂) :
    Reduction.challengeInY adversary g₁ Z₁ g₂ Z₂ =
      reductionY weight scalar (extracted (view adversary g₁)) g₁ Z₁ g₂ Z₂ := by
  unfold Reduction.challengeInY reductionY extracted
  apply bind_congr
  intro x
  apply bind_congr
  intro ρ
  have hsign : simSignY weight scalar g₁ Z₁ x ρ = fun m => (ρ m.1 * x) • g₁ + (ρ m.1 * m.2) • Z₁ := by
    funext m
    simp only [simSignY, muW_weight, scalar]
  rw [hsign]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply bind_congr
  rintro ⟨out, tr⟩
  simp only [guessY, known_eq, D_eq, D'_eq]

omit [Fintype F] [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem challengeInHashes_eq (Z₁ : G₁) (g₂ Z₂ : G₂) :
    Reduction.challengeInHashes adversary g₁ Z₁ g₂ Z₂ =
      reductionBad weight scalar attacked (extracted (view adversary g₁)) g₁ Z₁ g₂ Z₂ := by
  unfold Reduction.challengeInHashes reductionBad extracted
  apply bind_congr
  intro x
  apply bind_congr
  intro y
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  have hsign : realSign weight scalar x y (fun i => a i • Z₁ + b i • g₁) =
      fun m => (x + y * m.2) • (a m.1 • Z₁ + b m.1 • g₁) := by
    funext m
    simp only [realSign, LinFunctional.realSign, sum_weight_smul, scalar]
  simp only [hsign, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply bind_congr
  rintro ⟨out, tr⟩
  simp only [badDenom_eq]
  split_ifs <;> rfl

end Solvers

/-- Synchronized PS security for finite periods, with the three explicit solvers. -/
theorem security (g₁ : G₁) (g₂ : G₂) (adversary : Reduction.Adversary F Period G₁ G₂)
    (hgen : Function.Bijective (fun ρ : F => ρ • g₁))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    𝒟[lazyGame (Gₜ := Gₜ) g₁ g₂ (view adversary g₁)] {true} ≤
      Model.dlog11Advantage g₁ g₂ (Reduction.challengeInX adversary) +
      Model.dlog11Advantage g₁ g₂ (Reduction.challengeInY adversary) +
      Model.dlog11Advantage g₁ g₂ (Reduction.challengeInHashes adversary) +
      1 / (Fintype.card F : ENNReal) := by
  rw [lazyGame_eq_realGame]
  have h := adaptive_security (Gₜ := Gₜ) weight scalar g₁ g₂ (extracted (view adversary g₁)) valid attacked
    hgen (fun fo hv hf => nondegenerate fo hv hf) hpair
  have hX : Model.dlog11Advantage g₁ g₂ (Reduction.challengeInX adversary) =
      Pr[= true | dlog11Exp g₁ g₂ (reductionX weight scalar (extracted (view adversary g₁)))] := by
    rw [Model.dlog11Advantage, evalDist_apply_singleton]
    congr 1
    unfold dlog11Exp
    exact bind_congr fun α => by rw [challengeInX_eq]
  have hY : Model.dlog11Advantage g₁ g₂ (Reduction.challengeInY adversary) =
      Pr[= true | dlog11Exp g₁ g₂ (reductionY weight scalar (extracted (view adversary g₁)))] := by
    rw [Model.dlog11Advantage, evalDist_apply_singleton]
    congr 1
    unfold dlog11Exp
    exact bind_congr fun α => by rw [challengeInY_eq]
  have hH : Model.dlog11Advantage g₁ g₂ (Reduction.challengeInHashes adversary) =
      Pr[= true | dlog11Exp g₁ g₂ (reductionBad weight scalar attacked (extracted (view adversary g₁)))] := by
    rw [Model.dlog11Advantage, evalDist_apply_singleton]
    congr 1
    unfold dlog11Exp
    exact bind_congr fun α => by rw [challengeInHashes_eq]
  rw [hX, hY, hH]
  exact h

end SynchronizedPS.Proofs
