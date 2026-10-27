import Proofs.LinearFunctional.Adaptive

/-! # Two secrets, one hashed base: adaptive AGM extraction for synchronized PS

Signatures are `(x + y·s(m)) • Σᵢ wᵢ(m) Hᵢ`. A forgery on `m*` with co-signer offset `c`
verifies when `e(σ*, g₂) = e(Σᵢ wᵢ(m*) Hᵢ, (x + y·s(m*) + c)•g₂)`. With the base table `ρ`
known, the forgery's exponent is affine in the two secrets, `const + lin·x + lin'·y`, where
`lin'` uses the weights `w·s`, and verification reads `x·D + y·D' = K` with `D`, `D'` the
denominators of the weight families `w` and `w·s`. Three straight-line `(1,1)`-DLog reductions
cover the cases: the challenge as `x` (`D ≠ 0`), as `y` (`D' ≠ 0`), or hidden in the bases
(`D = D' = 0`, where a nonzero coordinate of one coefficient vector costs `1/|F|`). The proof
follows `LinearFunctional/Adaptive.lean`; the representation producer sees the concrete keys,
bases and signatures before answering. -/

open BilinearGroup OracleComp AlgebraicGroupModel AlgebraicGroupModel.LinFunctional Finset

namespace SynchronizedPS.Proofs

variable {F M ι : Type} [Field F] [SampleableType F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]
variable {G₁ G₂ Gₜ : Type}
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

/-- An exact-length algebraic forgery together with the co-signers' offset. -/
structure OffsetForgery (F M ι : Type) where
  rep : DynForgery F M ι
  offset : F

/-- The attacker as a representation producer: concrete keys, bases and signing function in. -/
abbrev AdaptiveAdv (F M ι G₁ G₂ : Type) :=
  (G₂ × G₂) → (ι → G₁) → (M → G₁) → ProbComp (OffsetForgery F M ι)

/-- The weight family of the second secret. -/
def scaled (w : ι → M → F) (s : M → F) : ι → M → F := fun i m => w i m * s m

/-- Honest signing with both secrets. -/
def realSign (w : ι → M → F) (s : M → F) (x y : F) (H : ι → G₁) (m : M) : G₁ :=
  LinFunctional.realSign w (x + y * s m) H m

variable (w : ι → M → F) (s : M → F)

/-! ## Real and scalar games -/

noncomputable def realGame (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂) :
    ProbComp (OffsetForgery F M ι × (F × F) × (ι → G₁) × (M → G₁)) := do
  let x ← ($ᵗ F : ProbComp F)
  let y ← ($ᵗ F : ProbComp F)
  let H ← ($ᵗ (ι → G₁) : ProbComp (ι → G₁))
  let fo ← adv (x • g₂, y • g₂) H (realSign w s x y H)
  pure (fo, (x, y), H, realSign w s x y H)

/-- Pairing verification against the honest key, the message scalar and the offset, with
freshness. -/
def succ (g₁ : G₁) (g₂ : G₂) (z : OffsetForgery F M ι × (F × F) × (ι → G₁) × (M → G₁)) : Prop :=
  pairing (F := F) (Gₜ := Gₜ) (dynForgeryElem g₁ z.1.rep z.2.2.1 z.2.2.2) g₂ =
    pairing (F := F) (Gₜ := Gₜ) (dynTargetElem w z.1.rep z.2.2.1)
      ((z.2.1.1 + z.2.1.2 * s z.1.rep.2.mstar + z.1.offset) • g₂) ∧ z.1.rep.Fresh

noncomputable def scalarGame (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂) :
    ProbComp (OffsetForgery F M ι × (F × F) × (ι → F)) := do
  let x ← ($ᵗ F : ProbComp F)
  let y ← ($ᵗ F : ProbComp F)
  let ρ ← ($ᵗ (ι → F) : ProbComp (ι → F))
  let fo ← adv (x • g₂, y • g₂) (fun i => ρ i • g₁) (realSign w s x y (fun i => ρ i • g₁))
  pure (fo, (x, y), ρ)

def mapScalar (g₁ : G₁) (z : OffsetForgery F M ι × (F × F) × (ι → F)) :
    OffsetForgery F M ι × (F × F) × (ι → G₁) × (M → G₁) :=
  (z.1, z.2.1, fun i => z.2.2 i • g₁, realSign w s z.2.1.1 z.2.1.2 (fun i => z.2.2 i • g₁))

omit [DecidableEq F] [Fintype G₁] in
/-- Programming the bases as `ρᵢ•g₁` for uniform `ρ` is the real game. -/
theorem realGame_eq_map_scalar (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂)
    (hgen : Function.Bijective (fun ρ : F => ρ • g₁)) :
    𝒮[realGame w s g₂ adv] = 𝒮[mapScalar w s g₁ <$> scalarGame w s g₁ g₂ adv] := by
  have hf : Function.Bijective (fun ρ : ι → F => fun i => ρ i • g₁) :=
    (Equiv.piCongrRight fun _ => Equiv.ofBijective _ hgen).bijective
  simp only [realGame, scalarGame, mapScalar, map_bind, map_pure]
  refine evalSPMF_bind_congr' _ fun x => ?_
  refine evalSPMF_bind_congr' _ fun y => ?_
  exact (evalSPMF_ext (probOutput_bind_bijective_uniform_cross (ι → F) _ hf
    (fun H => do
      let fo ← adv (x • g₂, y • g₂) H (realSign w s x y H)
      pure (fo, (x, y), H, realSign w s x y H)))).symm

/-! ## The scalar relation `x·D + y·D' = K` -/

omit [SampleableType F] [Fintype F] [DecidableEq F] [DecidableEq ι] [SampleableType G₁] [Fintype G₁] in
theorem muW_scaled (ρ : ι → F) (m : M) : muW (scaled w s) ρ m = muW w ρ m * s m := by
  simp only [muW, scaled, Finset.sum_mul, mul_assoc]

omit [SampleableType F] [Fintype F] [DecidableEq F] [DecidableEq ι] [SampleableType G₁] [Fintype G₁] in
theorem realSign_scalar (g₁ : G₁) (x y : F) (ρ : ι → F) (m : M) :
    realSign w s x y (fun i => ρ i • g₁) m = ((x + y * s m) * muW w ρ m) • g₁ := by
  rw [realSign, ← simSign_eq_realSign, simSign, smul_smul, mul_comm]

omit [SampleableType F] [Fintype F] [DecidableEq F] [DecidableEq ι] [SampleableType G₁] [Fintype G₁] in
/-- Under the scalar coupling the forged element has exponent `const + lin·x + lin'·y`. -/
theorem forgeryElem_scalar (g₁ : G₁) (fo : DynForgery F M ι) (x y : F) (ρ : ι → F) :
    dynForgeryElem g₁ fo (fun i => ρ i • g₁) (realSign w s x y (fun i => ρ i • g₁)) =
      ((dynReprA w fo ρ).const + (dynReprA w fo ρ).lin * x +
        (dynReprA (scaled w s) fo ρ).lin * y) • g₁ := by
  simp only [dynForgeryElem, forgeryElem, dynReprA, reprA, realSign_scalar, muW_scaled, smul_smul,
    ← Finset.sum_smul, ← add_smul]
  congr 1
  simp only [Finset.sum_mul, add_assoc]
  congr 2
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- The constant the reductions know: `const − c·μ(m*)`. -/
def known (fo : OffsetForgery F M ι) (ρ : ι → F) : F :=
  (dynReprA w fo.rep ρ).const - fo.offset * muW w ρ fo.rep.2.mstar

omit [SampleableType F] [Fintype F] [DecidableEq F] [DecidableEq ι] [SampleableType G₁] [Fintype G₁]
  [DecidableEq Gₜ] in
/-- A verifying forgery under the scalar coupling satisfies `x·D + y·D' = K`. -/
theorem relation (g₁ : G₁) (g₂ : G₂)
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ)))
    (z : OffsetForgery F M ι × (F × F) × (ι → F))
    (hsucc : succ (Gₜ := Gₜ) w s g₁ g₂ (mapScalar w s g₁ z)) :
    z.2.1.1 * dynDenom w z.1.rep z.2.2 + z.2.1.2 * dynDenom (scaled w s) z.1.rep z.2.2 =
      known w z.1 z.2.2 := by
  obtain ⟨fo, ⟨x, y⟩, ρ⟩ := z
  have hv := hsucc.1
  simp only [mapScalar, forgeryElem_scalar, dynTargetElem, targetElem_red] at hv
  have hrel := pairing_dlog_relation g₁ g₂
    (repr := ⟨(dynReprA w fo.rep ρ).const + (dynReprA w fo.rep ρ).lin * x +
      (dynReprA (scaled w s) fo.rep ρ).lin * y, 0⟩)
    (α := x + y * s fo.rep.2.mstar + fo.offset) (c := muW w ρ fo.rep.2.mstar)
    (by simp [AffineForm.eval]) hv hpair
  simp only [AffineForm.eval, zero_mul, add_zero] at hrel
  have hD : dynDenom w fo.rep ρ = muW w ρ fo.rep.2.mstar - (dynReprA w fo.rep ρ).lin := by
    rw [dynDenom, dynDenomCoeff, ← muW_sub_reprA_lin]
    rfl
  have hD' : dynDenom (scaled w s) fo.rep ρ =
      muW w ρ fo.rep.2.mstar * s fo.rep.2.mstar - (dynReprA (scaled w s) fo.rep ρ).lin := by
    rw [dynDenom, dynDenomCoeff, ← muW_sub_reprA_lin, muW_scaled]
    rfl
  simp only [known]
  rw [hD, hD']
  linear_combination -hrel

/-! ## Reading the challenge off the relation -/

def guessX (fo : OffsetForgery F M ι) (y : F) (ρ : ι → F) : F :=
  (known w fo ρ - y * dynDenom (scaled w s) fo.rep ρ) / dynDenom w fo.rep ρ

def guessY (fo : OffsetForgery F M ι) (x : F) (ρ : ι → F) : F :=
  (known w fo ρ - x * dynDenom w fo.rep ρ) / dynDenom (scaled w s) fo.rep ρ

/-- The zero-denominator branch: validity, freshness and `D = D' = 0`. -/
def badCore (valid : DynForgery F M ι → Prop) (fo : OffsetForgery F M ι) (ρ : ι → F) : Prop :=
  valid fo.rep ∧ fo.rep.Fresh ∧ dynDenom w fo.rep ρ = 0 ∧ dynDenom (scaled w s) fo.rep ρ = 0

omit [Fintype G₁] [DecidableEq Gₜ] in
theorem split (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂)
    (valid : DynForgery F M ι → Prop)
    (hgen : Function.Bijective (fun ρ : F => ρ • g₁))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    Pr[fun z => valid z.1.rep ∧ succ (Gₜ := Gₜ) w s g₁ g₂ z | realGame w s g₂ adv]
      ≤ Pr[fun z => guessX w s z.1 z.2.1.2 z.2.2 = z.2.1.1 | scalarGame w s g₁ g₂ adv]
        + Pr[fun z => guessY w s z.1 z.2.1.1 z.2.2 = z.2.1.2 | scalarGame w s g₁ g₂ adv]
        + Pr[fun z => badCore w s valid z.1 z.2.2 | scalarGame w s g₁ g₂ adv] := by
  rw [probEvent_def, realGame_eq_map_scalar w s g₁ g₂ adv hgen, ← probEvent_def, probEvent_map]
  refine le_trans (probEvent_mono ?_) (le_trans (probEvent_or_le _ _ _)
    (add_le_add (probEvent_or_le _ _ _) le_rfl))
  intro z _ hz
  obtain ⟨hvalid, hsucc⟩ := hz
  have hrel := relation w s g₁ g₂ hpair z hsucc
  by_cases hD : dynDenom w z.1.rep z.2.2 = 0
  · by_cases hD' : dynDenom (scaled w s) z.1.rep z.2.2 = 0
    · exact Or.inr ⟨hvalid, hsucc.2, hD, hD'⟩
    · refine Or.inl (Or.inr ?_)
      rw [guessY, div_eq_iff hD']
      linear_combination -hrel
  · refine Or.inl (Or.inl ?_)
    rw [guessX, div_eq_iff hD]
    linear_combination -hrel

/-! ## The two key reductions -/

/-- Simulated signing with the challenge as `x`: `μ(m)•Z₁ + (μ(m)·y·s(m))•g₁`. -/
def simSignX (g₁ Z₁ : G₁) (y : F) (ρ : ι → F) (m : M) : G₁ :=
  muW w ρ m • Z₁ + (muW w ρ m * (y * s m)) • g₁

/-- Simulated signing with the challenge as `y`: `(μ(m)·x)•g₁ + (μ(m)·s(m))•Z₁`. -/
def simSignY (g₁ Z₁ : G₁) (x : F) (ρ : ι → F) (m : M) : G₁ :=
  (muW w ρ m * x) • g₁ + (muW w ρ m * s m) • Z₁

omit [SampleableType F] [Fintype F] [DecidableEq F] [DecidableEq ι] [SampleableType G₁] [Fintype G₁] in
theorem simSignX_eq (g₁ : G₁) (x y : F) (ρ : ι → F) :
    simSignX w s g₁ (x • g₁) y ρ = realSign w s x y (fun i => ρ i • g₁) := by
  funext m
  rw [simSignX, realSign_scalar, smul_smul, ← add_smul]
  congr 1
  ring

omit [SampleableType F] [Fintype F] [DecidableEq F] [DecidableEq ι] [SampleableType G₁] [Fintype G₁] in
theorem simSignY_eq (g₁ : G₁) (x y : F) (ρ : ι → F) :
    simSignY w s g₁ (y • g₁) x ρ = realSign w s x y (fun i => ρ i • g₁) := by
  funext m
  rw [simSignY, realSign_scalar, smul_smul, ← add_smul]
  congr 1
  ring

noncomputable def reductionX (adv : AdaptiveAdv F M ι G₁ G₂) : DLog11Adversary F G₁ G₂ :=
  fun g₁ Z₁ g₂ Z₂ => do
    let y ← ($ᵗ F : ProbComp F)
    let ρ ← ($ᵗ (ι → F) : ProbComp (ι → F))
    let fo ← adv (Z₂, y • g₂) (fun i => ρ i • g₁) (simSignX w s g₁ Z₁ y ρ)
    pure (guessX w s fo y ρ)

noncomputable def reductionY (adv : AdaptiveAdv F M ι G₁ G₂) : DLog11Adversary F G₁ G₂ :=
  fun g₁ Z₁ g₂ Z₂ => do
    let x ← ($ᵗ F : ProbComp F)
    let ρ ← ($ᵗ (ι → F) : ProbComp (ι → F))
    let fo ← adv (x • g₂, Z₂) (fun i => ρ i • g₁) (simSignY w s g₁ Z₁ x ρ)
    pure (guessY w s fo x ρ)

omit [SampleableType G₁] [Fintype G₁] [Fintype F] in
theorem guessX_eq_dlog (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂) :
    Pr[fun z => guessX w s z.1 z.2.1.2 z.2.2 = z.2.1.1 | scalarGame w s g₁ g₂ adv]
      = Pr[= true | dlog11Exp g₁ g₂ (reductionX w s adv)] := by
  rw [← probEvent_eq_eq_probOutput]
  simp only [scalarGame, dlog11Exp, reductionX, bind_assoc, pure_bind, probEvent_bind_eq_tsum,
    probEvent_pure, decide_eq_true_eq, simSignX_eq]

omit [SampleableType G₁] [Fintype G₁] [Fintype F] in
theorem guessY_eq_dlog (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂) :
    Pr[fun z => guessY w s z.1 z.2.1.1 z.2.2 = z.2.1.2 | scalarGame w s g₁ g₂ adv]
      = Pr[= true | dlog11Exp g₁ g₂ (reductionY w s adv)] := by
  rw [← probEvent_eq_eq_probOutput]
  have hswap : 𝒮[scalarGame w s g₁ g₂ adv] = 𝒮[do
      let y ← ($ᵗ F : ProbComp F)
      let x ← ($ᵗ F : ProbComp F)
      let ρ ← ($ᵗ (ι → F) : ProbComp (ι → F))
      let fo ← adv (x • g₂, y • g₂) (fun i => ρ i • g₁) (realSign w s x y (fun i => ρ i • g₁))
      pure (fo, (x, y), ρ)] := by
    unfold scalarGame
    exact DeferredSampling.evalSPMF_bind_comm ($ᵗ F) ($ᵗ F) fun x y => do
      let ρ ← ($ᵗ (ι → F) : ProbComp (ι → F))
      let fo ← adv (x • g₂, y • g₂) (fun i => ρ i • g₁) (realSign w s x y (fun i => ρ i • g₁))
      pure (fo, (x, y), ρ)
  rw [probEvent_def, hswap, ← probEvent_def]
  simp only [dlog11Exp, reductionY, bind_assoc, pure_bind, probEvent_bind_eq_tsum,
    probEvent_pure, decide_eq_true_eq, simSignY_eq]

/-! ## The hash-table reduction for `D = D' = 0` -/

section Bad
variable (jk : DynForgery F M ι → ι)

/-- The coefficient vector the hash-branch reduction solves with: `D`'s unless its entry at the
attacked coordinate vanishes, then `D'`'s. -/
def badCoeff (fo : DynForgery F M ι) : ι → F :=
  if dynDenomCoeff w fo (jk fo) ≠ 0 then dynDenomCoeff w fo else dynDenomCoeff (scaled w s) fo

def badDenom (fo : DynForgery F M ι) (ρ : ι → F) : F := ∑ i, badCoeff w s jk fo i * ρ i

omit [SampleableType F] [Fintype F] [DecidableEq ι] [SampleableType G₁] [Fintype G₁] in
theorem badDenom_eq_zero (fo : DynForgery F M ι) (ρ : ι → F)
    (hD : dynDenom w fo ρ = 0) (hD' : dynDenom (scaled w s) fo ρ = 0) :
    badDenom w s jk fo ρ = 0 := by
  rw [dynDenom] at hD hD'
  unfold badDenom badCoeff
  split_ifs
  · exact hD
  · exact hD'

omit [SampleableType F] [Fintype F] [Fintype ι] [DecidableEq ι] [SampleableType G₁] [Fintype G₁] in
theorem badCoeff_ne_zero (fo : DynForgery F M ι)
    (h : dynDenomCoeff w fo (jk fo) ≠ 0 ∨ dynDenomCoeff (scaled w s) fo (jk fo) ≠ 0) :
    badCoeff w s jk fo (jk fo) ≠ 0 := by
  unfold badCoeff
  split_ifs with h₁
  · exact h₁
  · exact h.resolve_left h₁

omit [SampleableType F] [Fintype F] [DecidableEq ι] [SampleableType G₁] [Fintype G₁] in
theorem badDenom_affine (fo : DynForgery F M ι) (z : F) (a b : ι → F) :
    badDenom w s jk fo (affineTable z a b) = badDenom w s jk fo a * z + badDenom w s jk fo b := by
  simp only [badDenom, affineTable, mul_add, mul_assoc, Finset.sum_add_distrib, Finset.sum_mul]

/-- Both keys known, the challenge hidden in every base as `aᵢ•Z + bᵢ•g₁`. -/
noncomputable def reductionBad (adv : AdaptiveAdv F M ι G₁ G₂) : DLog11Adversary F G₁ G₂ :=
  fun g₁ Z g₂ _ => do
    let x ← ($ᵗ F : ProbComp F)
    let y ← ($ᵗ F : ProbComp F)
    let a ← ($ᵗ (ι → F) : ProbComp (ι → F))
    let b ← ($ᵗ (ι → F) : ProbComp (ι → F))
    let H := fun i => a i • Z + b i • g₁
    let fo ← adv (x • g₂, y • g₂) H (realSign w s x y H)
    pure (-badDenom w s jk fo.rep b / badDenom w s jk fo.rep a)

structure BadView (F M ι : Type) where
  fo : OffsetForgery F M ι
  keys : F × F
  challenge : F
  slope : ι → F
  table : ι → F

def BadView.scalar (v : BadView F M ι) : OffsetForgery F M ι × (F × F) × (ι → F) :=
  (v.fo, v.keys, v.table)

noncomputable def affineBadView (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂) :
    ProbComp (BadView F M ι) := do
  let z ← ($ᵗ F : ProbComp F)
  let x ← ($ᵗ F : ProbComp F)
  let y ← ($ᵗ F : ProbComp F)
  let a ← ($ᵗ (ι → F) : ProbComp (ι → F))
  let b ← ($ᵗ (ι → F) : ProbComp (ι → F))
  let ρ := affineTable z a b
  let fo ← adv (x • g₂, y • g₂) (fun i => ρ i • g₁) (realSign w s x y (fun i => ρ i • g₁))
  pure ⟨fo, (x, y), z, a, ρ⟩

noncomputable def independentBadView (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂) :
    ProbComp (BadView F M ι) := do
  let z ← ($ᵗ F : ProbComp F)
  let x ← ($ᵗ F : ProbComp F)
  let y ← ($ᵗ F : ProbComp F)
  let ρ ← ($ᵗ (ι → F) : ProbComp (ι → F))
  let fo ← adv (x • g₂, y • g₂) (fun i => ρ i • g₁) (realSign w s x y (fun i => ρ i • g₁))
  let a ← ($ᵗ (ι → F) : ProbComp (ι → F))
  pure ⟨fo, (x, y), z, a, ρ⟩

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] in
theorem independentBadView_scalar (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂) :
    𝒮[BadView.scalar <$> independentBadView w s g₁ g₂ adv] = 𝒮[scalarGame w s g₁ g₂ adv] := by
  unfold independentBadView scalarGame BadView.scalar
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  rw [DeferredSampling.evalSPMF_bind_const_neverFails ($ᵗ F) (by simp)]
  refine evalSPMF_bind_congr' _ fun x => ?_
  refine evalSPMF_bind_congr' _ fun y => ?_
  refine evalSPMF_bind_congr' _ fun ρ => ?_
  refine evalSPMF_bind_congr' _ fun fo => ?_
  rw [DeferredSampling.evalSPMF_bind_const_neverFails ($ᵗ (ι → F)) (by simp)]

def badGuess (v : BadView F M ι) : F :=
  -(badDenom w s jk v.fo.rep v.table - badDenom w s jk v.fo.rep v.slope * v.challenge) /
    badDenom w s jk v.fo.rep v.slope

omit [SampleableType F] [Fintype F] [DecidableEq ι] [SampleableType G₁] [Fintype G₁] in
theorem badGuess_eq (v : BadView F M ι) (hzero : badDenom w s jk v.fo.rep v.table = 0)
    (hslope : badDenom w s jk v.fo.rep v.slope ≠ 0) : badGuess w s jk v = v.challenge := by
  rw [badGuess, hzero, zero_sub, neg_neg, mul_div_cancel_left₀ _ hslope]

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] in
/-- Affine programming of the bases is a one-time pad: the slopes stay hidden. -/
theorem affineBadView_eq_independent (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂) :
    𝒮[affineBadView w s g₁ g₂ adv] = 𝒮[independentBadView w s g₁ g₂ adv] := by
  unfold affineBadView independentBadView
  refine evalSPMF_bind_congr' _ fun z => ?_
  refine evalSPMF_bind_congr' _ fun x => ?_
  refine evalSPMF_bind_congr' _ fun y => ?_
  trans 𝒮[do
    let a ← ($ᵗ (ι → F) : ProbComp (ι → F))
    let ρ ← ($ᵗ (ι → F) : ProbComp (ι → F))
    let fo ← adv (x • g₂, y • g₂) (fun i => ρ i • g₁) (realSign w s x y (fun i => ρ i • g₁))
    pure (BadView.mk fo (x, y) z a ρ)]
  · refine evalSPMF_bind_congr' _ fun a => ?_
    unfold affineTable
    simpa only [Pi.add_def, Pi.add_apply] using
      evalSPMF_ext (probOutput_bind_add_left_uniform (ι → F) (fun i => a i * z)
        (fun ρ : ι → F => do
          let fo ← adv (x • g₂, y • g₂) (fun i => ρ i • g₁) (realSign w s x y (fun i => ρ i • g₁))
          pure (BadView.mk fo (x, y) z a ρ)))
  · let seen : ProbComp (OffsetForgery F M ι × (ι → F)) := do
      let ρ ← ($ᵗ (ι → F) : ProbComp (ι → F))
      let fo ← adv (x • g₂, y • g₂) (fun i => ρ i • g₁) (realSign w s x y (fun i => ρ i • g₁))
      pure (fo, ρ)
    simpa only [seen, bind_assoc, pure_bind] using
      DeferredSampling.evalSPMF_bind_comm ($ᵗ (ι → F) : ProbComp (ι → F)) seen
        (fun a q => pure (BadView.mk q.1 (x, y) z a q.2))

omit [Fintype F] [SampleableType G₁] [Fintype G₁] in
theorem badGuess_eq_dlog (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂) :
    Pr[fun v => badGuess w s jk v = v.challenge | affineBadView w s g₁ g₂ adv]
      = Pr[= true | dlog11Exp g₁ g₂ (reductionBad w s jk adv)] := by
  have hH (z : F) (a b : ι → F) : (fun i => a i • (z • g₁) + b i • g₁) =
      (fun i => affineTable z a b i • g₁) := by
    funext i
    simp only [affineTable, add_smul, smul_smul]
  rw [← probEvent_eq_eq_probOutput]
  simp only [affineBadView, dlog11Exp, reductionBad, bind_assoc, pure_bind,
    probEvent_bind_eq_tsum, probEvent_pure, decide_eq_true_eq, hH,
    badGuess, badDenom_affine, add_sub_cancel_left]

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] in
theorem bad_core_scalar_eq_independent (valid : DynForgery F M ι → Prop)
    (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂) :
    Pr[fun z => badCore w s valid z.1 z.2.2 | scalarGame w s g₁ g₂ adv]
      = Pr[fun v => badCore w s valid v.fo v.table | independentBadView w s g₁ g₂ adv] := by
  have hdist := independentBadView_scalar w s g₁ g₂ adv
  rw [probEvent_def, ← hdist, ← probEvent_def, probEvent_map]
  rfl

omit [SampleableType G₁] [Fintype G₁] in
theorem independent_slope_collision (valid : DynForgery F M ι → Prop)
    (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂)
    (hvand : ∀ fo, valid fo → fo.Fresh →
      dynDenomCoeff w fo (jk fo) ≠ 0 ∨ dynDenomCoeff (scaled w s) fo (jk fo) ≠ 0) :
    Pr[fun v => badCore w s valid v.fo v.table ∧ badDenom w s jk v.fo.rep v.slope = 0 |
        independentBadView w s g₁ g₂ adv]
      ≤ 1 / (Fintype.card F : ENNReal) := by
  rw [independentBadView]
  refine probEvent_bind_le_of_forall_le fun z _ => ?_
  refine probEvent_bind_le_of_forall_le fun x _ => ?_
  refine probEvent_bind_le_of_forall_le fun y _ => ?_
  refine probEvent_bind_le_of_forall_le fun ρ _ => ?_
  refine probEvent_bind_le_of_forall_le fun fo _ => ?_
  rw [bind_pure_comp, probEvent_map]
  by_cases hcore : badCore w s valid fo ρ
  · simpa only [Function.comp_def, hcore, true_and, badDenom] using
      linear_functional_collision (badCoeff w s jk fo.rep) (jk fo.rep)
        (badCoeff_ne_zero w s jk fo.rep (hvand fo.rep hcore.1 hcore.2.1)) 0
  · simp [Function.comp_def, hcore]

omit [SampleableType G₁] [Fintype G₁] in
theorem bad_core_le_dlog_add_collision (valid : DynForgery F M ι → Prop)
    (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂)
    (hvand : ∀ fo, valid fo → fo.Fresh →
      dynDenomCoeff w fo (jk fo) ≠ 0 ∨ dynDenomCoeff (scaled w s) fo (jk fo) ≠ 0) :
    Pr[fun z => badCore w s valid z.1 z.2.2 | scalarGame w s g₁ g₂ adv]
      ≤ Pr[= true | dlog11Exp g₁ g₂ (reductionBad w s jk adv)] + 1 / (Fintype.card F : ENNReal) := by
  rw [bad_core_scalar_eq_independent w s valid g₁ g₂ adv]
  refine le_trans (probEvent_mono ?_) (le_trans
    (probEvent_or_le (independentBadView w s g₁ g₂ adv)
      (fun v => badGuess w s jk v = v.challenge)
      (fun v => badCore w s valid v.fo v.table ∧ badDenom w s jk v.fo.rep v.slope = 0)) ?_)
  · intro v _ hcore
    by_cases hslope : badDenom w s jk v.fo.rep v.slope = 0
    · exact Or.inr ⟨hcore, hslope⟩
    · exact Or.inl (badGuess_eq w s jk v
        (badDenom_eq_zero w s jk v.fo.rep v.table hcore.2.2.1 hcore.2.2.2) hslope)
  · have hguess := badGuess_eq_dlog w s jk g₁ g₂ adv
    rw [probEvent_def, affineBadView_eq_independent, ← probEvent_def] at hguess
    rw [hguess]
    exact add_le_add le_rfl (independent_slope_collision w s jk valid g₁ g₂ adv hvand)

end Bad

omit [Fintype G₁] [DecidableEq Gₜ] in
/-- **Three-reduction theorem.** The real success of a representation producer is bounded by three
explicit straight-line `(1,1)`-DLog reductions plus the hidden-slope collision `1/|F|`. -/
theorem adaptive_security (g₁ : G₁) (g₂ : G₂) (adv : AdaptiveAdv F M ι G₁ G₂)
    (valid : DynForgery F M ι → Prop) (jk : DynForgery F M ι → ι)
    (hgen : Function.Bijective (fun ρ : F => ρ • g₁))
    (hvand : ∀ fo, valid fo → fo.Fresh →
      dynDenomCoeff w fo (jk fo) ≠ 0 ∨ dynDenomCoeff (scaled w s) fo (jk fo) ≠ 0)
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    Pr[fun z => valid z.1.rep ∧ succ (Gₜ := Gₜ) w s g₁ g₂ z | realGame w s g₂ adv]
      ≤ Pr[= true | dlog11Exp g₁ g₂ (reductionX w s adv)]
        + Pr[= true | dlog11Exp g₁ g₂ (reductionY w s adv)]
        + Pr[= true | dlog11Exp g₁ g₂ (reductionBad w s jk adv)]
        + 1 / (Fintype.card F : ENNReal) := by
  have hsplit := split w s g₁ g₂ adv valid hgen hpair
  rw [guessX_eq_dlog, guessY_eq_dlog] at hsplit
  have hbad := bad_core_le_dlog_add_collision w s jk valid g₁ g₂ adv hvand
  calc _ ≤ _ := hsplit
    _ ≤ _ := add_le_add le_rfl hbad
    _ = _ := by simp only [add_assoc]

end SynchronizedPS.Proofs
