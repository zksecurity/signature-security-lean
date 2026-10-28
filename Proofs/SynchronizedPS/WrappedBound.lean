import Proofs.SynchronizedPS.WrappedSecurity

/-! The synchronized PS bound by the four wrapped weighted solvers. The pivot run is read as the
synchronized scalar game and as the two weighted scalar games (one key fixed); the four pointwise
cases give four event probabilities, each the success of a weighted solver on the wrapped attacker
with the known key sampled first, the bad ones with the hidden-slope collision. -/

open BilinearGroup OracleComp OracleSpec AlgebraicGroupModel AlgebraicGroupModel.LinFunctional
open Model Model.LazyAGM Model.LazyAGM.Proofs Model.LazyAGM.WeightedReduction SynchronizedPS.Proofs
open BLS.LazyAGM.Reduction (dlog11Advantage_congr)

namespace SynchronizedPS.Wrapped

variable {F Period G₁ G₂ Gₜ : Type}
  [Field F] [SampleableType F] [Fintype F] [DecidableEq F] [Fintype Period] [DecidableEq Period]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

local instance : MeasurableSpace F := ⊤

variable (V : Proofs.View F Period G₁ G₂) (g₁ : G₁) (g₂ : G₂)

/-! ## Sums over the pivot -/

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem pivot_tsum (q : ((Output F (Forgery F Period) × List (Event F Period)) × (Period → F)) × F × F → Prop) :
    Pr[q | pivot V g₁ g₂] =
      ∑' x : F, Pr[= x | ($ᵗ F : ProbComp F)] * ∑' y : F, Pr[= y | ($ᵗ F : ProbComp F)] *
        Pr[fun w => q (w, x, y) | body V g₁ g₂ x y] := by
  unfold pivot
  simp only [probEvent_bind_eq_tsum, bind_pure_comp, probEvent_map, Function.comp_def]

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
/-- Sampling the known key inside the solver is averaging the solver's success over it. -/
theorem dlog_bind_uniform (B : F → G₁ → G₁ → G₂ → G₂ → ProbComp F) :
    Pr[= true | dlog11Exp g₁ g₂ (fun h₁ Z₁ h₂ Z₂ => do let k ← ($ᵗ F : ProbComp F); B k h₁ Z₁ h₂ Z₂)] =
      ∑' k : F, Pr[= k | ($ᵗ F : ProbComp F)] * Pr[= true | dlog11Exp g₁ g₂ (B k)] := by
  classical
  simp only [dlog11Exp, bind_assoc, ← probEvent_eq_eq_probOutput, probEvent_bind_eq_tsum,
    ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => tsum_congr fun α => tsum_congr fun r => ?_
  ring

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
/-- Scheme₁'s scalar game at `y` as a sum over the pivot's run. -/
theorem scalarGame₁_tsum (y : F) (q : DynForgery F (Period × F) Period × F × (Period → F) → Prop) :
    Pr[q | scalarGameDynAdaptive weight g₁ g₂ (Model.LazyAGM.Proofs.extracted (wrap₁ y g₂ V))] =
      ∑' x : F, Pr[= x | ($ᵗ F : ProbComp F)] * Pr[fun w => q (forgery₁ g₁ x y w, x, w.2) | body V g₁ g₂ x y] := by
  rw [scalarGame₁_eq]
  simp only [probEvent_bind_eq_tsum, bind_pure_comp, probEvent_map, Function.comp_def]

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem scalarGame₂_tsum (x : F) (q : DynForgery F (Period × F) Period × F × (Period → F) → Prop) :
    Pr[q | scalarGameDynAdaptive (scaled weight scalar) g₁ g₂ (Model.LazyAGM.Proofs.extracted (wrap₂ x g₂ V))] =
      ∑' y : F, Pr[= y | ($ᵗ F : ProbComp F)] * Pr[fun w => q (forgery₂ g₁ x y w, y, w.2) | body V g₁ g₂ x y] := by
  rw [scalarGame₂_eq]
  simp only [probEvent_bind_eq_tsum, bind_pure_comp, probEvent_map, Function.comp_def]

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
/-- An event on the pivot that only reads scheme₁'s view is the `y`-average of the scheme₁ game. -/
theorem pivot_eq_average₁ (q : DynForgery F (Period × F) Period × F × (Period → F) → Prop) :
    Pr[fun t => q (forgery₁ g₁ t.2.1 t.2.2 t.1, t.2.1, t.1.2) | pivot V g₁ g₂] =
      ∑' y : F, Pr[= y | ($ᵗ F : ProbComp F)] *
        Pr[q | scalarGameDynAdaptive weight g₁ g₂ (Model.LazyAGM.Proofs.extracted (wrap₁ y g₂ V))] := by
  rw [pivot_tsum]
  simp only [scalarGame₁_tsum, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun y => tsum_congr fun x => ?_
  ring

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem pivot_eq_average₂ (q : DynForgery F (Period × F) Period × F × (Period → F) → Prop) :
    Pr[fun t => q (forgery₂ g₁ t.2.1 t.2.2 t.1, t.2.2, t.1.2) | pivot V g₁ g₂] =
      ∑' x : F, Pr[= x | ($ᵗ F : ProbComp F)] *
        Pr[q | scalarGameDynAdaptive (scaled weight scalar) g₁ g₂ (Model.LazyAGM.Proofs.extracted (wrap₂ x g₂ V))] := by
  rw [pivot_tsum]
  simp only [scalarGame₂_tsum]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype Period] [DecidableEq Period] [AddCommGroup G₁] [Module F G₁]
  [SampleableType G₁] [Fintype G₁] [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
/-- Averaging a per-key bound with a constant loss keeps the loss once. -/
theorem tsum_probOutput_mul_add_le (a : F → ENNReal) (c : ENNReal) :
    ∑' y : F, Pr[= y | ($ᵗ F : ProbComp F)] * (a y + c) ≤ (∑' y : F, Pr[= y | ($ᵗ F : ProbComp F)] * a y) + c := by
  rw [show (∑' y : F, Pr[= y | ($ᵗ F : ProbComp F)] * (a y + c)) =
      (∑' y : F, Pr[= y | ($ᵗ F : ProbComp F)] * a y) + (∑' y : F, Pr[= y | ($ᵗ F : ProbComp F)]) * c by
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
    exact tsum_congr fun y => mul_add _ _ _]
  gcongr
  calc (∑' y : F, Pr[= y | ($ᵗ F : ProbComp F)]) * c ≤ 1 * c := by gcongr; exact tsum_probOutput_le_one
    _ = c := one_mul c

/-! ## The bound -/

/-- The synchronized win, read on the pivot. -/
def wins (t : ((Output F (Forgery F Period) × List (Event F Period)) × (Period → F)) × F × F) : Prop :=
  Proofs.valid (syncForgery g₁ t.2.1 t.2.2 t.1).rep ∧
    succ (Gₜ := Gₜ) weight scalar g₁ g₂
      (mapScalar weight scalar g₁ (syncForgery g₁ t.2.1 t.2.2 t.1, (t.2.1, t.2.2), t.1.2))

theorem lazyGame_eq_pivot (hgen : Function.Bijective (fun ρ : F => ρ • g₁)) :
    𝒟[lazyGame (Gₜ := Gₜ) g₁ g₂ V] {true} = Pr[wins (Gₜ := Gₜ) g₁ g₂ | pivot V g₁ g₂] := by
  rw [lazyGame_eq_realGame, probEvent_def, realGame_eq_map_scalar weight scalar g₁ g₂ _ hgen, ← probEvent_def,
    probEvent_map, scalarGame_eq, probEvent_map]
  rfl

/-- Scheme₁'s good extraction event. -/
def good₁ (t : DynForgery F (Period × F) Period × F × (Period → F)) : Prop :=
  (dynReprA weight t.1 t.2.2).const / (muW weight t.2.2 t.1.2.mstar - (dynReprA weight t.1 t.2.2).lin) = t.2.1

def good₂ (t : DynForgery F (Period × F) Period × F × (Period → F)) : Prop :=
  (dynReprA (scaled weight scalar) t.1 t.2.2).const /
    (muW (scaled weight scalar) t.2.2 t.1.2.mstar - (dynReprA (scaled weight scalar) t.1 t.2.2).lin) = t.2.1

def bad₁ (t : DynForgery F (Period × F) Period × F × (Period → F)) : Prop :=
  adaptiveBadCore valid₁ weight t.1 t.2.2

def bad₂ (t : DynForgery F (Period × F) Period × F × (Period → F)) : Prop :=
  adaptiveBadCore valid₂ (scaled weight scalar) t.1 t.2.2

omit [SampleableType F] [Fintype F] [SampleableType G₁] [Fintype G₁] [DecidableEq Gₜ] in
/-- Every synchronized win falls in one of the four cases. -/
theorem wins_cases (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ)))
    (t : ((Output F (Forgery F Period) × List (Event F Period)) × (Period → F)) × F × F)
    (h : wins (Gₜ := Gₜ) g₁ g₂ t) :
    good₁ (forgery₁ g₁ t.2.1 t.2.2 t.1, t.2.1, t.1.2) ∨ bad₁ (forgery₁ g₁ t.2.1 t.2.2 t.1, t.2.1, t.1.2) ∨
      good₂ (forgery₂ g₁ t.2.1 t.2.2 t.1, t.2.2, t.1.2) ∨ bad₂ (forgery₂ g₁ t.2.1 t.2.2 t.1, t.2.2, t.1.2) := by
  obtain ⟨w, x, y⟩ := t
  obtain ⟨hvalid, hsucc⟩ := h
  by_cases hD : Reduction.D w.1.1 (syncTranscript g₁ x y w) w.2 = 0
  · by_cases hreuse : Reduction.reuse w.1.1 (syncTranscript g₁ x y w) = 0
    · by_cases hD' : Reduction.D' w.1.1 (syncTranscript g₁ x y w) w.2 = 0
      · exact Or.inr (Or.inr (Or.inr (bad₂_of g₁ g₂ x y w hsucc hvalid hD' hreuse)))
      · exact Or.inr (Or.inr (Or.inl (good₂_of g₁ g₂ x y w hpair hsucc hD')))
    · exact Or.inr (Or.inl (bad₁_of g₁ g₂ x y w hsucc hD hreuse))
  · exact Or.inl (good₁_of g₁ g₂ x y w hpair hsucc hD)

/-- The adaptive forms of the four solvers. -/
noncomputable def adaptiveGood₁ : DLog11Adversary F G₁ G₂ := fun g₁ Z₁ g₂ Z₂ => do
  let y ← ($ᵗ F : ProbComp F)
  adaptiveGoodDlogReduction weight (Model.LazyAGM.Proofs.extracted (wrap₁ y g₂ V)) g₁ Z₁ g₂ Z₂
noncomputable def adaptiveBad₁ : DLog11Adversary F G₁ G₂ := fun g₁ Z₁ g₂ Z₂ => do
  let y ← ($ᵗ F : ProbComp F)
  adaptiveBadDlogReduction weight (Model.LazyAGM.Proofs.extracted (wrap₁ y g₂ V)) g₁ Z₁ g₂ Z₂
noncomputable def adaptiveGood₂ : DLog11Adversary F G₁ G₂ := fun g₁ Z₁ g₂ Z₂ => do
  let x ← ($ᵗ F : ProbComp F)
  adaptiveGoodDlogReduction (scaled weight scalar) (Model.LazyAGM.Proofs.extracted (wrap₂ x g₂ V)) g₁ Z₁ g₂ Z₂
noncomputable def adaptiveBad₂ : DLog11Adversary F G₁ G₂ := fun g₁ Z₁ g₂ Z₂ => do
  let x ← ($ᵗ F : ProbComp F)
  adaptiveBadDlogReduction (scaled weight scalar) (Model.LazyAGM.Proofs.extracted (wrap₂ x g₂ V)) g₁ Z₁ g₂ Z₂

omit [Fintype F] [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]
  [DecidableEq Gₜ] in
theorem good₁_bound :
    Pr[fun t => good₁ (forgery₁ g₁ t.2.1 t.2.2 t.1, t.2.1, t.1.2) | pivot V g₁ g₂] =
      Pr[= true | dlog11Exp g₁ g₂ (adaptiveGood₁ V)] := by
  rw [pivot_eq_average₁]
  unfold adaptiveGood₁
  rw [dlog_bind_uniform]
  refine tsum_congr fun y => congrArg _ ?_
  exact adaptive_good_extract_eq_dlog weight g₁ g₂ _

omit [Fintype F] [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]
  [DecidableEq Gₜ] in
theorem good₂_bound :
    Pr[fun t => good₂ (forgery₂ g₁ t.2.1 t.2.2 t.1, t.2.2, t.1.2) | pivot V g₁ g₂] =
      Pr[= true | dlog11Exp g₁ g₂ (adaptiveGood₂ V)] := by
  rw [pivot_eq_average₂]
  unfold adaptiveGood₂
  rw [dlog_bind_uniform]
  refine tsum_congr fun x => congrArg _ ?_
  exact adaptive_good_extract_eq_dlog (scaled weight scalar) g₁ g₂ _

omit [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]
  [DecidableEq Gₜ] in
theorem bad₁_bound :
    Pr[fun t => bad₁ (forgery₁ g₁ t.2.1 t.2.2 t.1, t.2.1, t.1.2) | pivot V g₁ g₂] ≤
      Pr[= true | dlog11Exp g₁ g₂ (adaptiveBad₁ V)] + 1 / (Fintype.card F : ENNReal) := by
  rw [pivot_eq_average₁]
  unfold adaptiveBad₁
  rw [dlog_bind_uniform]
  have each : ∀ y : F, Pr[bad₁ | scalarGameDynAdaptive weight g₁ g₂ (Model.LazyAGM.Proofs.extracted (wrap₁ y g₂ V))] ≤
      Pr[= true | dlog11Exp g₁ g₂ (adaptiveBadDlogReduction weight (Model.LazyAGM.Proofs.extracted (wrap₁ y g₂ V)))] +
        1 / (Fintype.card F : ENNReal) := fun y =>
    adaptive_bad_core_le_dlog_add_collision valid₁ weight g₁ g₂ _ (fun fo => fo.2.mstar.1) (fun _ hv _ => hv)
  calc _ ≤ ∑' y : F, Pr[= y | ($ᵗ F : ProbComp F)] *
        (Pr[= true | dlog11Exp g₁ g₂ (adaptiveBadDlogReduction weight (Model.LazyAGM.Proofs.extracted (wrap₁ y g₂ V)))] +
          1 / (Fintype.card F : ENNReal)) := ENNReal.tsum_le_tsum fun y => by gcongr; exact each y
    _ ≤ _ := tsum_probOutput_mul_add_le _ _

omit [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]
  [DecidableEq Gₜ] in
theorem bad₂_bound :
    Pr[fun t => bad₂ (forgery₂ g₁ t.2.1 t.2.2 t.1, t.2.2, t.1.2) | pivot V g₁ g₂] ≤
      Pr[= true | dlog11Exp g₁ g₂ (adaptiveBad₂ V)] + 1 / (Fintype.card F : ENNReal) := by
  rw [pivot_eq_average₂]
  unfold adaptiveBad₂
  rw [dlog_bind_uniform]
  have each : ∀ x : F, Pr[bad₂ | scalarGameDynAdaptive (scaled weight scalar) g₁ g₂
        (Model.LazyAGM.Proofs.extracted (wrap₂ x g₂ V))] ≤
      Pr[= true | dlog11Exp g₁ g₂ (adaptiveBadDlogReduction (scaled weight scalar)
        (Model.LazyAGM.Proofs.extracted (wrap₂ x g₂ V)))] + 1 / (Fintype.card F : ENNReal) := fun x =>
    adaptive_bad_core_le_dlog_add_collision valid₂ (scaled weight scalar) g₁ g₂ _ (fun fo => fo.2.mstar.1)
      valid₂_nondegenerate
  calc _ ≤ ∑' x : F, Pr[= x | ($ᵗ F : ProbComp F)] *
        (Pr[= true | dlog11Exp g₁ g₂ (adaptiveBadDlogReduction (scaled weight scalar)
          (Model.LazyAGM.Proofs.extracted (wrap₂ x g₂ V)))] + 1 / (Fintype.card F : ENNReal)) :=
        ENNReal.tsum_le_tsum fun x => by gcongr; exact each x
    _ ≤ _ := tsum_probOutput_mul_add_le _ _

/-! ## The adaptive solvers are the list-cache solvers -/

omit [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem adaptiveGood₁_advantage :
    Model.dlog11Advantage g₁ g₂ (adaptiveGood₁ V) = Model.dlog11Advantage g₁ g₂ (solverGood₁ V) := by
  apply dlog11Advantage_congr
  intro α
  unfold adaptiveGood₁ solverGood₁
  refine evalDist_bind_congr _ _ _ fun y => ?_
  rw [← goodReduction_eq, goodReductionList_eq, goodReductionLazy_eq_eager terms₁ weight termsValue₁]

omit [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem adaptiveBad₁_advantage :
    Model.dlog11Advantage g₁ g₂ (adaptiveBad₁ V) = Model.dlog11Advantage g₁ g₂ (solverBad₁ V) := by
  apply dlog11Advantage_congr
  intro α
  unfold adaptiveBad₁ solverBad₁
  refine evalDist_bind_congr _ _ _ fun y => ?_
  rw [← badReduction_eq, badReductionList_eq, badReductionLazy_eq_eager terms₁ weight termsValue₁]

omit [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem adaptiveGood₂_advantage :
    Model.dlog11Advantage g₁ g₂ (adaptiveGood₂ V) = Model.dlog11Advantage g₁ g₂ (solverGood₂ V) := by
  apply dlog11Advantage_congr
  intro α
  unfold adaptiveGood₂ solverGood₂
  refine evalDist_bind_congr _ _ _ fun x => ?_
  rw [← goodReduction_eq, goodReductionList_eq, goodReductionLazy_eq_eager terms₂ (scaled weight scalar) termsValue₂]

omit [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem adaptiveBad₂_advantage :
    Model.dlog11Advantage g₁ g₂ (adaptiveBad₂ V) = Model.dlog11Advantage g₁ g₂ (solverBad₂ V) := by
  apply dlog11Advantage_congr
  intro α
  unfold adaptiveBad₂ solverBad₂
  refine evalDist_bind_congr _ _ _ fun x => ?_
  rw [← badReduction_eq, badReductionList_eq, badReductionLazy_eq_eager terms₂ (scaled weight scalar) termsValue₂]

/-- **Synchronized PS security from the four wrapped weighted solvers.** -/
theorem security_wrapped (hgen : Function.Bijective (fun ρ : F => ρ • g₁))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    𝒟[lazyGame (Gₜ := Gₜ) g₁ g₂ V] {true} ≤
      Model.dlog11Advantage g₁ g₂ (solverGood₁ V) + Model.dlog11Advantage g₁ g₂ (solverBad₁ V) +
      Model.dlog11Advantage g₁ g₂ (solverGood₂ V) + Model.dlog11Advantage g₁ g₂ (solverBad₂ V) +
      2 / (Fintype.card F : ENNReal) := by
  rw [lazyGame_eq_pivot V g₁ g₂ hgen, ← adaptiveGood₁_advantage, ← adaptiveBad₁_advantage,
    ← adaptiveGood₂_advantage, ← adaptiveBad₂_advantage]
  simp only [Model.dlog11Advantage, evalDist_apply_singleton]
  let E₁ := fun t : ((Output F (Forgery F Period) × List (Event F Period)) × (Period → F)) × F × F =>
    good₁ (forgery₁ g₁ t.2.1 t.2.2 t.1, t.2.1, t.1.2)
  let E₂ := fun t : ((Output F (Forgery F Period) × List (Event F Period)) × (Period → F)) × F × F =>
    bad₁ (forgery₁ g₁ t.2.1 t.2.2 t.1, t.2.1, t.1.2)
  let E₃ := fun t : ((Output F (Forgery F Period) × List (Event F Period)) × (Period → F)) × F × F =>
    good₂ (forgery₂ g₁ t.2.1 t.2.2 t.1, t.2.2, t.1.2)
  let E₄ := fun t : ((Output F (Forgery F Period) × List (Event F Period)) × (Period → F)) × F × F =>
    bad₂ (forgery₂ g₁ t.2.1 t.2.2 t.1, t.2.2, t.1.2)
  have split : Pr[wins (Gₜ := Gₜ) g₁ g₂ | pivot V g₁ g₂] ≤
      Pr[E₁ | pivot V g₁ g₂] + Pr[E₂ | pivot V g₁ g₂] +
      Pr[E₃ | pivot V g₁ g₂] + Pr[E₄ | pivot V g₁ g₂] := by
    refine le_trans (probEvent_mono fun t _ h => wins_cases g₁ g₂ hpair t h) ?_
    calc Pr[fun t => E₁ t ∨ E₂ t ∨ E₃ t ∨ E₄ t | pivot V g₁ g₂]
        ≤ Pr[E₁ | pivot V g₁ g₂] + Pr[fun t => E₂ t ∨ E₃ t ∨ E₄ t | pivot V g₁ g₂] :=
          probEvent_or_le _ _ _
      _ ≤ Pr[E₁ | pivot V g₁ g₂] +
          (Pr[E₂ | pivot V g₁ g₂] + Pr[fun t => E₃ t ∨ E₄ t | pivot V g₁ g₂]) :=
          add_le_add le_rfl (probEvent_or_le _ _ _)
      _ ≤ Pr[E₁ | pivot V g₁ g₂] +
          (Pr[E₂ | pivot V g₁ g₂] + (Pr[E₃ | pivot V g₁ g₂] + Pr[E₄ | pivot V g₁ g₂])) :=
          add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le _ _ _))
      _ = _ := by ring
  refine split.trans ?_
  rw [good₁_bound, good₂_bound]
  have b₁ := bad₁_bound V g₁ g₂
  have b₂ := bad₂_bound V g₁ g₂
  calc _ ≤ Pr[= true | dlog11Exp g₁ g₂ (adaptiveGood₁ V)] +
        (Pr[= true | dlog11Exp g₁ g₂ (adaptiveBad₁ V)] + 1 / (Fintype.card F : ENNReal)) +
        Pr[= true | dlog11Exp g₁ g₂ (adaptiveGood₂ V)] +
        (Pr[= true | dlog11Exp g₁ g₂ (adaptiveBad₂ V)] + 1 / (Fintype.card F : ENNReal)) :=
      add_le_add (add_le_add (add_le_add le_rfl b₁) le_rfl) b₂
    _ = _ := by
      rw [show (2 : ENNReal) / (Fintype.card F : ENNReal) = 1 / (Fintype.card F : ENNReal) + 1 / (Fintype.card F : ENNReal) by
        rw [ENNReal.div_add_div_same, one_add_one_eq_two]]
      ring

end SynchronizedPS.Wrapped
