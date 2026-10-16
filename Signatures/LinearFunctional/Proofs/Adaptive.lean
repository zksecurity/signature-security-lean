/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.LinearFunctional.Proofs.Dynamic

/-!
# Adaptive AGM extraction for linear-functional signatures

The representation producer below receives the concrete public base table and signing function before it
returns its exact-length algebraic representation.  Its messages, coefficients, target, and control
flow may therefore depend arbitrarily on all concrete group values it has seen.

The proof uses two straight-line `(1,1)`-DLog reductions.

* If the verification denominator `D` is nonzero, the usual reduction extracts the signing key.
* If `D = 0`, a second reduction chooses a known signing key and programs every base as
  `H i = a i • X + b i • g₁`.  The masks `b` make the public table perfectly uniform.  After the
  table is fixed, the slope table `a` is still uniform and hidden from the adversary.  Vandermonde
  non-degeneracy supplies a nonzero coefficient of `D`, so the probability that its slope is zero
  is at most `1 / |F|`; otherwise the same relation reveals the DLog of `X`.

No target, message, coefficient, or base is fixed before the adversary runs, and no rewinding is
used.
-/

open BilinearGroup

open OracleComp AlgebraicGroupModel Finset

namespace AlgebraicGroupModel.LinFunctional

variable {F M ι : Type} [Field F] [SampleableType F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

variable {G₁ G₂ Gₜ : Type}
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

/-- A fully adaptive exact-length algebraic representation producer.  It sees the concrete public
key, every concrete public base, and the concrete signing function before producing its output. -/
abbrev AdaptiveAdv (F M ι G₁ G₂ : Type) :=
  G₂ → (ι → G₁) → (M → G₁) → ProbComp (DynForgery F M ι)

/-- The real adaptive representation game. -/
noncomputable def realGameDynAdaptive (w : ι → M → F) (g₂ : G₂)
    (adv : AdaptiveAdv F M ι G₁ G₂) :
    ProbComp (DynForgery F M ι × F × (ι → G₁) × (M → G₁)) := do
  let α ← ($ᵗ F : ProbComp F)
  let H ← ($ᵗ (ι → G₁) : ProbComp (ι → G₁))
  let fo ← adv (α • g₂) H (realSign w α H)
  pure (fo, α, H, realSign w α H)

/-- Scalar-programmed view: the adversary runs after the scalar table has been materialized
as concrete group elements. -/
noncomputable def scalarGameDynAdaptive (w : ι → M → F) (g₁ : G₁) (g₂ : G₂)
    (adv : AdaptiveAdv F M ι G₁ G₂) :
    ProbComp (DynForgery F M ι × F × (ι → F)) := do
  let α ← ($ᵗ F : ProbComp F)
  let ρ ← ($ᵗ (ι → F) : ProbComp (ι → F))
  let fo ← adv (α • g₂) (fun i => ρ i • g₁) (simSign w (α • g₁) ρ)
  pure (fo, α, ρ)

/-- Interpret a scalar-game sample as a concrete real-game sample. -/
def mapScalarDyn (w : ι → M → F) (g₁ : G₁)
    (x : DynForgery F M ι × F × (ι → F)) :
    DynForgery F M ι × F × (ι → G₁) × (M → G₁) :=
  (x.1, x.2.1, (fun i => x.2.2 i • g₁), simSign w (x.2.1 • g₁) x.2.2)

omit [DecidableEq F] in
/-- Perfect simulation remains valid when the complete algebraic output depends on the concrete
bases and signatures. -/
theorem realGameDynAdaptive_eq_map_scalar (w : ι → M → F) (g₁ : G₁) (g₂ : G₂)
    (adv : AdaptiveAdv F M ι G₁ G₂)
    (hgen : Function.Bijective (fun ρ : F => ρ • g₁)) :
    𝒮[realGameDynAdaptive w g₂ adv]
      = 𝒮[mapScalarDyn w g₁ <$> scalarGameDynAdaptive w g₁ g₂ adv] := by
  simp only [realGameDynAdaptive, scalarGameDynAdaptive, mapScalarDyn, map_bind, map_pure]
  refine evalSPMF_bind_congr' _ fun α => ?_
  exact (functional_perfect_sim w g₁ α hgen
    (fun H signO => do
      let fo ← adv (α • g₂) H signO
      pure (fo, α, H, signO))).symm

/-- The usual nonzero-denominator DLog reduction, now running the representation producer after it
has received the concrete programmed bases and signature replies. -/
noncomputable def adaptiveGoodDlogReduction (w : ι → M → F)
    (adv : AdaptiveAdv F M ι G₁ G₂) : DLog11Adversary F G₁ G₂ :=
  fun g₁ X₁ _ X₂ => do
    let ρ ← ($ᵗ (ι → F) : ProbComp (ι → F))
    let fo ← adv X₂ (fun i => ρ i • g₁) (simSign w X₁ ρ)
    pure ((dynReprA w fo ρ).const /
      (muW w ρ fo.2.mstar - (dynReprA w fo ρ).lin))

omit [SampleableType G₁] [Fintype G₁] [Fintype F] in
/-- The good extraction event is exactly the success event of `adaptiveGoodDlogReduction`. -/
theorem adaptive_good_extract_eq_dlog (w : ι → M → F) (g₁ : G₁) (g₂ : G₂)
    (adv : AdaptiveAdv F M ι G₁ G₂) :
    Pr[fun x => (dynReprA w x.1 x.2.2).const /
          (muW w x.2.2 x.1.2.mstar - (dynReprA w x.1 x.2.2).lin) = x.2.1 |
        scalarGameDynAdaptive w g₁ g₂ adv]
      = Pr[= true | dlog11Exp g₁ g₂ (adaptiveGoodDlogReduction w adv)] := by
  rw [← probEvent_eq_eq_probOutput]
  simp only [scalarGameDynAdaptive, dlog11Exp, adaptiveGoodDlogReduction, bind_assoc, pure_bind,
    probEvent_bind_eq_tsum, probEvent_pure, decide_eq_true_eq]

omit [DecidableEq Gₜ] in
/-- Adaptive perfect simulation followed by the algebraic extraction split.  This theorem leaves
the `D = 0` executions explicit; `adaptive_bad_core_le_dlog_add_collision` discharges them with a
second straight-line reduction. -/
theorem functional_euf_cma_adaptive_split (w : ι → M → F) (g₁ : G₁) (g₂ : G₂)
    (adv : AdaptiveAdv F M ι G₁ G₂) (valid : DynForgery F M ι → Prop)
    (hgen : Function.Bijective (fun ρ : F => ρ • g₁))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    Pr[fun x => valid x.1 ∧ dynForgerySucc (Gₜ := Gₜ) w g₁ g₂ x |
        realGameDynAdaptive w g₂ adv]
      ≤ Pr[fun x => (dynReprA w x.1 x.2.2).const /
            (muW w x.2.2 x.1.2.mstar - (dynReprA w x.1 x.2.2).lin) = x.2.1 |
          scalarGameDynAdaptive w g₁ g₂ adv]
        + Pr[fun x => (valid x.1 ∧
              dynForgerySucc (Gₜ := Gₜ) w g₁ g₂ (mapScalarDyn w g₁ x)) ∧
              (dynReprA w x.1 x.2.2).lin = muW w x.2.2 x.1.2.mstar |
            scalarGameDynAdaptive w g₁ g₂ adv] := by
  rw [probEvent_def, realGameDynAdaptive_eq_map_scalar w g₁ g₂ adv hgen,
    ← probEvent_def, probEvent_map]
  exact agm_forgery_extract_split (scalarGameDynAdaptive w g₁ g₂ adv)
    (fun x => valid x.1 ∧
      dynForgerySucc (Gₜ := Gₜ) w g₁ g₂ (mapScalarDyn w g₁ x))
    (fun x => dynReprA w x.1 x.2.2)
    (fun x => muW w x.2.2 x.1.2.mstar) (fun x => x.2.1) (by
      intro x _ hsucc
      have hv := hsucc.2.1
      rw [mapScalarDyn, dynForgeryElem, dynTargetElem, forgeryElem_red, targetElem_red] at hv
      exact pairing_dlog_relation g₁ g₂ rfl hv hpair)

/-! ## The adaptive `D = 0` branch -/

/-- Affine scalar table hidden in bases `a i • X + b i • g₁`. -/
def affineTable (z : F) (a b : ι → F) : ι → F :=
  fun i => a i * z + b i

/-- The coefficient vector of the verification denominator. -/
def dynDenomCoeff (w : ι → M → F) (fo : DynForgery F M ι) : ι → F :=
  Lcoeff w fo.2.mstar fo.2.v fo.2.ξ

/-- Its inner product with a scalar table. -/
def dynDenom (w : ι → M → F) (fo : DynForgery F M ι) (ρ : ι → F) : F :=
  ∑ i, dynDenomCoeff w fo i * ρ i

/-- The slope of the denominator under affine programming. -/
def dynDenomSlope (w : ι → M → F) (fo : DynForgery F M ι) (a : ι → F) : F :=
  ∑ i, dynDenomCoeff w fo i * a i

/-- The masked constant term of the denominator under affine programming. -/
def dynDenomMask (w : ι → M → F) (fo : DynForgery F M ι) (b : ι → F) : F :=
  ∑ i, dynDenomCoeff w fo i * b i

omit [SampleableType F] [Fintype F] [DecidableEq F] [DecidableEq ι] in
@[simp]
theorem dynDenom_affine (w : ι → M → F) (fo : DynForgery F M ι)
    (z : F) (a b : ι → F) :
    dynDenom w fo (affineTable z a b)
      = dynDenomSlope w fo a * z + dynDenomMask w fo b := by
  simp only [dynDenom, affineTable, dynDenomSlope, dynDenomMask, mul_add,
    mul_assoc, Finset.sum_add_distrib, Finset.sum_mul]

/-- The straight-line DLog reduction for the zero-denominator branch.  It knows the OOPS signing
key `κ`; the DLog challenge is hidden only in the public base table. -/
noncomputable def adaptiveBadDlogReduction (w : ι → M → F)
    (adv : AdaptiveAdv F M ι G₁ G₂) : DLog11Adversary F G₁ G₂ :=
  fun g₁ X g₂ _ => do
    let κ ← ($ᵗ F : ProbComp F)
    let a ← ($ᵗ (ι → F) : ProbComp (ι → F))
    let b ← ($ᵗ (ι → F) : ProbComp (ι → F))
    let H := fun i => a i • X + b i • g₁
    let fo ← adv (κ • g₂) H (realSign w κ H)
    pure (-dynDenomMask w fo b / dynDenomSlope w fo a)

/-- Common scalar view used to couple affine programming to an independent uniform base table. -/
structure AdaptiveBadView (F M ι : Type) where
  fo : DynForgery F M ι
  key : F
  challenge : F
  slope : ι → F
  table : ι → F

/-- Forget the independent affine challenge and slope, retaining the scalar-game sample. -/
def AdaptiveBadView.scalar (v : AdaptiveBadView F M ι) :
    DynForgery F M ι × F × (ι → F) :=
  (v.fo, v.key, v.table)

/-- The view induced by the actual affine DLog reduction. -/
noncomputable def adaptiveAffineBadView (w : ι → M → F) (g₁ : G₁) (g₂ : G₂)
    (adv : AdaptiveAdv F M ι G₁ G₂) : ProbComp (AdaptiveBadView F M ι) := do
  let z ← ($ᵗ F : ProbComp F)
  let κ ← ($ᵗ F : ProbComp F)
  let a ← ($ᵗ (ι → F) : ProbComp (ι → F))
  let b ← ($ᵗ (ι → F) : ProbComp (ι → F))
  let ρ := affineTable z a b
  let fo ← adv (κ • g₂) (fun i => ρ i • g₁) (realSign w κ (fun i => ρ i • g₁))
  pure ⟨fo, κ, z, a, ρ⟩

/-- Reparameterized affine view: the public table is sampled first and is independent of the
hidden slope table. -/
noncomputable def adaptiveIndependentBadView (w : ι → M → F) (g₁ : G₁) (g₂ : G₂)
    (adv : AdaptiveAdv F M ι G₁ G₂) : ProbComp (AdaptiveBadView F M ι) := do
  let z ← ($ᵗ F : ProbComp F)
  let κ ← ($ᵗ F : ProbComp F)
  let ρ ← ($ᵗ (ι → F) : ProbComp (ι → F))
  let fo ← adv (κ • g₂) (fun i => ρ i • g₁) (realSign w κ (fun i => ρ i • g₁))
  let a ← ($ᵗ (ι → F) : ProbComp (ι → F))
  pure ⟨fo, κ, z, a, ρ⟩

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] in
/-- Projecting the reparameterized view gives exactly the scalar game.  The two extra uniform
samples are never-failing and are erased; simulator signatures are converted to honest signatures
by the pointwise perfect-simulation identity. -/
theorem adaptiveIndependentBadView_scalar (w : ι → M → F) (g₁ : G₁) (g₂ : G₂)
    (adv : AdaptiveAdv F M ι G₁ G₂) :
    𝒮[AdaptiveBadView.scalar <$> adaptiveIndependentBadView w g₁ g₂ adv]
      = 𝒮[scalarGameDynAdaptive w g₁ g₂ adv] := by
  unfold adaptiveIndependentBadView scalarGameDynAdaptive AdaptiveBadView.scalar
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  rw [DeferredSampling.evalSPMF_bind_const_neverFails ($ᵗ F) (by simp)]
  refine evalSPMF_bind_congr' _ fun κ => ?_
  refine evalSPMF_bind_congr' _ fun ρ => ?_
  have hs : simSign w (κ • g₁) ρ = realSign w κ (fun i => ρ i • g₁) := by
    funext m
    exact simSign_eq_realSign w g₁ κ ρ m
  rw [hs]
  refine evalSPMF_bind_congr' _ fun fo => ?_
  rw [DeferredSampling.evalSPMF_bind_const_neverFails ($ᵗ (ι → F)) (by simp)]

/-- The scalar expression output by the affine reduction, written in the common view.  The mask
table is `b = ρ - a*z`; spelling it this way is only for the coupling proof--the reduction itself
knows the originally sampled `b`. -/
def adaptiveBadGuess (w : ι → M → F) (v : AdaptiveBadView F M ι) : F :=
  -(dynDenom w v.fo v.table - dynDenomSlope w v.fo v.slope * v.challenge) /
    dynDenomSlope w v.fo v.slope

omit [SampleableType F] [Fintype F] [DecidableEq F] [DecidableEq ι]
  [SampleableType G₁] [Fintype G₁] [DecidableEq Gₜ] in
/-- On a zero-denominator execution, every nonzero affine slope reveals the hidden challenge. -/
theorem adaptiveBadGuess_eq_of_denom_zero (w : ι → M → F) (v : AdaptiveBadView F M ι)
    (hzero : dynDenom w v.fo v.table = 0)
    (hslope : dynDenomSlope w v.fo v.slope ≠ 0) :
    adaptiveBadGuess w v = v.challenge := by
  rw [adaptiveBadGuess, hzero, zero_sub, neg_neg, mul_div_cancel_left₀ _ hslope]

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] in
/-- Affine programming is a perfect one-time-pad reparameterization.  In particular, even though
the adversary sees and branches on the concrete base and signature values, its output and the
resulting denominator coefficient vector are independent of the hidden slope table. -/
theorem adaptiveAffineBadView_eq_independent (w : ι → M → F) (g₁ : G₁) (g₂ : G₂)
    (adv : AdaptiveAdv F M ι G₁ G₂) :
    𝒮[adaptiveAffineBadView w g₁ g₂ adv]
      = 𝒮[adaptiveIndependentBadView w g₁ g₂ adv] := by
  unfold adaptiveAffineBadView adaptiveIndependentBadView
  refine evalSPMF_bind_congr' _ fun z => ?_
  refine evalSPMF_bind_congr' _ fun κ => ?_
  trans 𝒮[do
    let a ← ($ᵗ (ι → F) : ProbComp (ι → F))
    let ρ ← ($ᵗ (ι → F) : ProbComp (ι → F))
    let fo ← adv (κ • g₂) (fun i => ρ i • g₁)
      (realSign w κ (fun i => ρ i • g₁))
    pure (AdaptiveBadView.mk fo κ z a ρ)]
  · refine evalSPMF_bind_congr' _ fun a => ?_
    unfold affineTable
    simpa only [Pi.add_def, Pi.add_apply] using
      evalSPMF_ext (probOutput_bind_add_left_uniform (ι → F) (fun i => a i * z)
        (fun ρ : ι → F => do
          let fo ← adv (κ • g₂) (fun i => ρ i • g₁)
            (realSign w κ (fun i => ρ i • g₁))
          pure (AdaptiveBadView.mk fo κ z a ρ)))
  · let seen : ProbComp (DynForgery F M ι × (ι → F)) := do
      let ρ ← ($ᵗ (ι → F) : ProbComp (ι → F))
      let fo ← adv (κ • g₂) (fun i => ρ i • g₁)
        (realSign w κ (fun i => ρ i • g₁))
      pure (fo, ρ)
    simpa only [seen, bind_assoc, pure_bind] using
      DeferredSampling.evalSPMF_bind_comm ($ᵗ (ι → F) : ProbComp (ι → F)) seen
        (fun a q => pure (AdaptiveBadView.mk q.1 κ z a q.2))

omit [Fintype F] [SampleableType G₁] [Fintype G₁] in
/-- The success event of the affine branch's concrete DLog adversary is exactly the challenge-guess
event in `adaptiveAffineBadView`. -/
theorem adaptive_bad_guess_eq_dlog (w : ι → M → F) (g₁ : G₁) (g₂ : G₂)
    (adv : AdaptiveAdv F M ι G₁ G₂) :
    Pr[fun v => adaptiveBadGuess w v = v.challenge | adaptiveAffineBadView w g₁ g₂ adv]
      = Pr[= true | dlog11Exp g₁ g₂ (adaptiveBadDlogReduction w adv)] := by
  have hH (z : F) (a b : ι → F) : (fun i => a i • (z • g₁) + b i • g₁) =
      (fun i => affineTable z a b i • g₁) := by
    funext i
    simp only [affineTable, add_smul, smul_smul]
  rw [← probEvent_eq_eq_probOutput]
  simp only [adaptiveAffineBadView, dlog11Exp, adaptiveBadDlogReduction, bind_assoc, pure_bind,
    probEvent_bind_eq_tsum, probEvent_pure, decide_eq_true_eq, hH,
    adaptiveBadGuess, dynDenom_affine, add_sub_cancel_left]

/-- The only information needed in the zero-denominator branch: game validity, exact transcript
freshness, and `D = 0`. -/
def adaptiveBadCore (valid : DynForgery F M ι → Prop) (w : ι → M → F)
    (fo : DynForgery F M ι) (ρ : ι → F) : Prop :=
  valid fo ∧ fo.Fresh ∧ dynDenom w fo ρ = 0

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] in
/-- Adding the independent challenge and slope samples does not change the probability of the bad
core event. -/
theorem adaptive_bad_core_scalar_eq_independent (valid : DynForgery F M ι → Prop)
    (w : ι → M → F) (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂) :
    Pr[fun x => adaptiveBadCore valid w x.1 x.2.2 |
        scalarGameDynAdaptive w g₁ g₂ adv]
      = Pr[fun v => adaptiveBadCore valid w v.fo v.table |
          adaptiveIndependentBadView w g₁ g₂ adv] := by
  have hdist := adaptiveIndependentBadView_scalar w g₁ g₂ adv
  rw [probEvent_def, ← hdist, ← probEvent_def, probEvent_map]
  rfl

omit [SampleableType G₁] [Fintype G₁] in
/-- Once the concrete public table, transcript, target, and coefficients have been fixed, the
hidden affine slope is a nonzero linear functional of an independent uniform table. -/
theorem adaptive_independent_slope_collision (valid : DynForgery F M ι → Prop)
    (w : ι → M → F) (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂)
    (jk : DynForgery F M ι → ι)
    (hvand : ∀ fo, valid fo → fo.Fresh → dynDenomCoeff w fo (jk fo) ≠ 0) :
    Pr[fun v => adaptiveBadCore valid w v.fo v.table ∧
          dynDenomSlope w v.fo v.slope = 0 |
        adaptiveIndependentBadView w g₁ g₂ adv]
      ≤ 1 / (Fintype.card F : ENNReal) := by
  rw [adaptiveIndependentBadView]
  refine probEvent_bind_le_of_forall_le fun z _ => ?_
  refine probEvent_bind_le_of_forall_le fun κ _ => ?_
  refine probEvent_bind_le_of_forall_le fun ρ _ => ?_
  refine probEvent_bind_le_of_forall_le fun fo _ => ?_
  rw [bind_pure_comp, probEvent_map]
  by_cases hcore : adaptiveBadCore valid w fo ρ
  · simpa only [Function.comp_def, hcore, true_and, dynDenomSlope] using
      linear_functional_collision (dynDenomCoeff w fo) (jk fo)
        (hvand fo hcore.1 hcore.2.1) 0
  · simp [Function.comp_def, hcore]

omit [SampleableType G₁] [Fintype G₁] in
/-- The complete adaptive zero-denominator bound.  It applies to a representation producer whose
target and coefficients may depend arbitrarily on the concrete group table and signing replies. -/
theorem adaptive_bad_core_le_dlog_add_collision (valid : DynForgery F M ι → Prop)
    (w : ι → M → F) (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂)
    (jk : DynForgery F M ι → ι)
    (hvand : ∀ fo, valid fo → fo.Fresh → dynDenomCoeff w fo (jk fo) ≠ 0) :
    Pr[fun x => adaptiveBadCore valid w x.1 x.2.2 |
        scalarGameDynAdaptive w g₁ g₂ adv]
      ≤ Pr[= true | dlog11Exp g₁ g₂ (adaptiveBadDlogReduction w adv)]
        + 1 / (Fintype.card F : ENNReal) := by
  rw [adaptive_bad_core_scalar_eq_independent valid w g₁ g₂ adv]
  refine le_trans (probEvent_mono ?_) (le_trans
    (probEvent_or_le (adaptiveIndependentBadView w g₁ g₂ adv)
      (fun v => adaptiveBadGuess w v = v.challenge)
      (fun v => adaptiveBadCore valid w v.fo v.table ∧
        dynDenomSlope w v.fo v.slope = 0)) ?_)
  · intro v _ hcore
    by_cases hslope : dynDenomSlope w v.fo v.slope = 0
    · exact Or.inr ⟨hcore, hslope⟩
    · exact Or.inl (adaptiveBadGuess_eq_of_denom_zero w v hcore.2.2 hslope)
  · have hguess := adaptive_bad_guess_eq_dlog w g₁ g₂ adv
    rw [probEvent_def, adaptiveAffineBadView_eq_independent, ← probEvent_def] at hguess
    rw [hguess]
    exact add_le_add le_rfl
      (adaptive_independent_slope_collision valid w g₁ g₂ adv jk hvand)

omit [DecidableEq Gₜ] in
/-- **Full adaptive two-reduction theorem.**  The representation producer runs after receiving the
concrete base table and signing function.  Its real success is bounded by two explicit straight-line
`(1,1)`-DLog reductions plus the single hidden-slope collision `1 / |F|`. -/
theorem functional_euf_cma_adaptive (w : ι → M → F) (g₁ : G₁) (g₂ : G₂)
    (adv : AdaptiveAdv F M ι G₁ G₂) (valid : DynForgery F M ι → Prop)
    (jk : DynForgery F M ι → ι)
    (hgen : Function.Bijective (fun ρ : F => ρ • g₁))
    (hvand : ∀ fo, valid fo → fo.Fresh → dynDenomCoeff w fo (jk fo) ≠ 0)
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    Pr[fun x => valid x.1 ∧ dynForgerySucc (Gₜ := Gₜ) w g₁ g₂ x |
        realGameDynAdaptive w g₂ adv]
      ≤ Pr[= true | dlog11Exp g₁ g₂ (adaptiveGoodDlogReduction w adv)]
        + Pr[= true | dlog11Exp g₁ g₂ (adaptiveBadDlogReduction w adv)]
        + 1 / (Fintype.card F : ENNReal) := by
  let badSplit :
      (DynForgery F M ι × F × (ι → F)) → Prop := fun x =>
    (valid x.1 ∧ dynForgerySucc (Gₜ := Gₜ) w g₁ g₂ (mapScalarDyn w g₁ x)) ∧
      (dynReprA w x.1 x.2.2).lin = muW w x.2.2 x.1.2.mstar
  have hbad :
      Pr[badSplit | scalarGameDynAdaptive w g₁ g₂ adv]
        ≤ Pr[fun x => adaptiveBadCore valid w x.1 x.2.2 |
            scalarGameDynAdaptive w g₁ g₂ adv] := by
    refine probEvent_mono ?_
    intro x _ hx
    refine ⟨hx.1.1, hx.1.2.2, ?_⟩
    rw [dynDenom, dynDenomCoeff, ← muW_sub_reprA_lin]
    change _ - (dynReprA w x.1 x.2.2).lin = 0
    rw [hx.2, sub_self]
  have hbadDlog := adaptive_bad_core_le_dlog_add_collision valid w g₁ g₂ adv jk hvand
  have hsplit := functional_euf_cma_adaptive_split w g₁ g₂ adv valid hgen hpair
  have hbound := hsplit.trans (add_le_add le_rfl (hbad.trans hbadDlog))
  simpa only [adaptive_good_extract_eq_dlog, add_assoc] using hbound

end AlgebraicGroupModel.LinFunctional
