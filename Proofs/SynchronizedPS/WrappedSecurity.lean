import Proofs.SynchronizedPS.WrappedAlgebra
import Proofs.LinearFunctional.LazyAGMCoupling

/-! Synchronized PS security from the two weighted schemes. The synchronized scalar game is the
attacker's ordered run under uniform keys and base table; the weighted scalar game of the wrapped
attacker is the same run with one key fixed. A valid forgery falls in one of four cases, each
caught by a weighted solver on the wrapped attacker: `D ≠ 0` (good₁), `D = 0 ∧ reuse ≠ 0` (bad₁),
`D' ≠ 0` otherwise (good₂), and `D = D' = 0 ∧ reuse = 0` (bad₂). The known key is sampled by the
solver, so every solver is `WeightedReduction.goodReductionList`/`badReductionList` on the wrapped
attacker, the programs the weighted Caliper pipeline executes. -/

open BilinearGroup OracleComp OracleSpec AlgebraicGroupModel AlgebraicGroupModel.LinFunctional
open Model Model.LazyAGM Model.LazyAGM.Proofs Model.LazyAGM.WeightedReduction SynchronizedPS.Proofs

namespace SynchronizedPS.Wrapped

variable {F Period G₁ G₂ Gₜ : Type}
  [Field F] [SampleableType F] [Fintype F] [DecidableEq F] [Fintype Period] [DecidableEq Period]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

/-! ## The two weighted schemes -/

/-- Scheme₁: hash `H(t)`, secret `x`. -/
def terms₁ (m : Period × F) : List (Period × F) := [(m.1, 1)]
/-- Scheme₂: hash `m•H(t)`, secret `y`. -/
def terms₂ (m : Period × F) : List (Period × F) := [(m.1, m.2)]

omit [SampleableType F] [Fintype F] [DecidableEq F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [Fintype G₁] [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]
  [DecidableEq Gₜ] in
theorem termsValue₁ (table : Period → F) (m : Period × F) :
    termsValue terms₁ table m = ∑ i, table i * weight i m := by
  simp [termsValue, terms₁, weight]

omit [SampleableType F] [Fintype F] [DecidableEq F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [Fintype G₁] [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]
  [DecidableEq Gₜ] in
theorem termsValue₂ (table : Period → F) (m : Period × F) :
    termsValue terms₂ table m = ∑ i, table i * scaled weight scalar i m := by
  simp [termsValue, terms₂, scaled, weight, scalar, mul_comm]

/-- Scheme₁'s correction `(y·m)•H(t)` and final `(y·m*)•H(t*)`. -/
def correction₁ (y : F) (m : Period × F) : F := y * m.2
def final₁ (y : F) (out : Forgery F Period) : F := y * out.2
/-- Scheme₂'s correction `x•H(t)` and final `x•H(t*)`. -/
def correction₂ (x : F) (_ : Period × F) : F := x
def final₂ (x : F) (_ : Forgery F Period) : F := x

/-- The attacker wrapped for scheme₁ with the known second key `y`. -/
def wrap₁ (y : F) (g₂ : G₂) (V : Proofs.View F Period G₁ G₂) :
    Model.LazyAGM.Adversary F Period (Period × F) G₁ G₂ :=
  wrap (correction₁ y) (final₁ y) (fun pk => (pk, y • g₂)) V

/-- The attacker wrapped for scheme₂ with the known first key `x`. -/
def wrap₂ (x : F) (g₂ : G₂) (V : Proofs.View F Period G₁ G₂) :
    Model.LazyAGM.Adversary F Period (Period × F) G₁ G₂ :=
  wrap (correction₂ x) (final₂ x) (fun pk => (x • g₂, pk)) V

/-- The four synchronized PS solvers: a weighted solver on the wrapped attacker, after sampling
the known key. -/
noncomputable def solverGood₁ (V : Proofs.View F Period G₁ G₂) : DLog11Adversary F G₁ G₂ :=
  fun g₁ Z₁ g₂ Z₂ => do
    let y ← ($ᵗ F : ProbComp F)
    goodReductionList terms₁ (wrap₁ y g₂ V) g₁ Z₁ g₂ Z₂

noncomputable def solverBad₁ (V : Proofs.View F Period G₁ G₂) : DLog11Adversary F G₁ G₂ :=
  fun g₁ Z₁ g₂ Z₂ => do
    let y ← ($ᵗ F : ProbComp F)
    badReductionList terms₁ (wrap₁ y g₂ V) g₁ Z₁ g₂ Z₂

noncomputable def solverGood₂ (V : Proofs.View F Period G₁ G₂) : DLog11Adversary F G₁ G₂ :=
  fun g₁ Z₁ g₂ Z₂ => do
    let x ← ($ᵗ F : ProbComp F)
    goodReductionList terms₂ (wrap₂ x g₂ V) g₁ Z₁ g₂ Z₂

noncomputable def solverBad₂ (V : Proofs.View F Period G₁ G₂) : DLog11Adversary F G₁ G₂ :=
  fun g₁ Z₁ g₂ Z₂ => do
    let x ← ($ᵗ F : ProbComp F)
    badReductionList terms₂ (wrap₂ x g₂ V) g₁ Z₁ g₂ Z₂

/-! ## One run, three games -/

variable (V : Proofs.View F Period G₁ G₂) (g₁ : G₁) (g₂ : G₂)

/-- The attacker's ordered run against the synchronized signer with keys `x, y` and table `ρ`. -/
noncomputable def body (x y : F) :
    ProbComp ((Output F (Forgery F Period) × List (Event F Period)) × (Period → F)) := do
  let ρ ← ($ᵗ (Period → F) : ProbComp (Period → F))
  let z ← orderedRun V (x • g₂, y • g₂) (fun i => ρ i • g₁) (fun m => (x + y * m.2) • (ρ m.1 • g₁))
  pure (z, ρ)

/-- Keys first, then the run. -/
noncomputable def pivot : ProbComp (((Output F (Forgery F Period) × List (Event F Period)) × (Period → F)) × F × F) := do
  let x ← ($ᵗ F : ProbComp F)
  let y ← ($ᵗ F : ProbComp F)
  let w ← body V g₁ g₂ x y
  pure (w, x, y)

/-- The synchronized signer at keys `x, y` over the table `ρ`. -/
abbrev syncSign (x y : F) (ρ : Period → F) : Period × F → G₁ := fun m => (x + y * m.2) • (ρ m.1 • g₁)

/-- The synchronized forgery of a run (its transcript points play no role). -/
def syncForgery (x y : F) (w : (Output F (Forgery F Period) × List (Event F Period)) × (Period → F)) :
    OffsetForgery F (Period × F) Period :=
  toOffsetForgery (w.1.1, transcript (fun i => w.2 i • g₁) (syncSign g₁ x y w.2) w.1.2)

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem scalarGame_eq :
    scalarGame weight scalar g₁ g₂ (SynchronizedPS.Proofs.extracted V) =
      (fun t => (syncForgery g₁ t.2.1 t.2.2 t.1, (t.2.1, t.2.2), t.1.2)) <$> pivot V g₁ g₂ := by
  unfold scalarGame SynchronizedPS.Proofs.extracted pivot body
  simp only [realSign_weight, run_eq_ordered, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  rfl

omit [SampleableType F] [Fintype F] [DecidableEq F] [SampleableType G₁]
  [Fintype G₁] [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]
  [DecidableEq Gₜ] in
theorem signing₁ (x y : F) (ρ : Period → F) :
    (fun m : Period × F => simSign weight (x • g₁) ρ m + (y * m.2) • (ρ m.1 • g₁)) = syncSign g₁ x y ρ := by
  funext m
  simp only [simSign, muW_weight, syncSign, smul_smul, ← add_smul]
  congr 1
  ring

omit [SampleableType F] [Fintype F] [DecidableEq F] [SampleableType G₁]
  [Fintype G₁] [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]
  [DecidableEq Gₜ] in
theorem signing₂ (x y : F) (ρ : Period → F) :
    (fun m : Period × F => simSign (scaled weight scalar) (y • g₁) ρ m + x • (ρ m.1 • g₁)) = syncSign g₁ x y ρ := by
  funext m
  simp only [simSign, muW_scaled, muW_weight, syncSign, scalar, smul_smul, ← add_smul]
  congr 1
  ring

/-- The base table of a run as points. -/
abbrev table (w : (Output F (Forgery F Period) × List (Event F Period)) × (Period → F)) : Period → G₁ :=
  fun i => w.2 i • g₁

/-- Scheme₁'s forgery from a run. -/
def forgery₁ (x y : F) (w : (Output F (Forgery F Period) × List (Event F Period)) × (Period → F)) :
    DynForgery F (Period × F) Period :=
  wrappedForgery (correction₁ y) (final₁ y) (table g₁ w) (simSign weight (x • g₁) w.2) w.1

/-- Scheme₂'s forgery from a run. -/
def forgery₂ (x y : F) (w : (Output F (Forgery F Period) × List (Event F Period)) × (Period → F)) :
    DynForgery F (Period × F) Period :=
  wrappedForgery (correction₂ x) (final₂ x) (table g₁ w) (simSign (scaled weight scalar) (y • g₁) w.2) w.1

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem scalarGame₁_eq (y : F) :
    scalarGameDynAdaptive weight g₁ g₂ (Model.LazyAGM.Proofs.extracted (wrap₁ y g₂ V)) = (do
      let x ← ($ᵗ F : ProbComp F)
      let w ← body V g₁ g₂ x y
      pure (forgery₁ g₁ x y w, x, w.2)) := by
  unfold scalarGameDynAdaptive Model.LazyAGM.Proofs.extracted wrap₁ body forgery₁
  simp only [fixedRun_wrap, correction₁, signing₁, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]

omit [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem scalarGame₂_eq (x : F) :
    scalarGameDynAdaptive (scaled weight scalar) g₁ g₂ (Model.LazyAGM.Proofs.extracted (wrap₂ x g₂ V)) = (do
      let y ← ($ᵗ F : ProbComp F)
      let w ← body V g₁ g₂ x y
      pure (forgery₂ g₁ x y w, y, w.2)) := by
  unfold scalarGameDynAdaptive Model.LazyAGM.Proofs.extracted wrap₂ body forgery₂
  simp only [fixedRun_wrap, correction₂, signing₂, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]

/-! ## The four cases, pointwise -/

/-- The synchronized transcript of a run. -/
abbrev syncTranscript (x y : F) (w : (Output F (Forgery F Period) × List (Event F Period)) × (Period → F)) :
    Transcript Period (Period × F) G₁ :=
  transcript (fun i => w.2 i • g₁) (syncSign g₁ x y w.2) w.1.2

section Pointwise
variable (x y : F) (w : (Output F (Forgery F Period) × List (Event F Period)) × (Period → F))

local notation "tr" => syncTranscript g₁ x y w

omit [SampleableType F] [Fintype F] [DecidableEq F] [Fintype Period] [DecidableEq Period] [SampleableType G₁]
  [Fintype G₁] [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]
  [DecidableEq Gₜ] in
theorem signSum_eq (c : Period × F → F) (ξ : List F) (events : List (Event F Period)) (ρ : Period → F) (j : Nat) :
    signSum ρ c ξ events j = ((messages events).mapIdx fun n m => tokenCoeff ξ (n + j) * c m * ρ m.1).sum := by
  induction events generalizing j with
  | nil => rfl
  | cons event rest ih =>
      cases event with
      | hash t => simp only [signSum, messages, ih]
      | sign m =>
          simp only [signSum, messages, List.mapIdx_cons, List.sum_cons, zero_add, ih (j + 1)]
          have shift : ∀ n (q : Period × F), tokenCoeff ξ (n + 1 + j) * c q * ρ q.1 =
              tokenCoeff ξ (n + (j + 1)) * c q * ρ q.1 := fun n q => by rw [Nat.add_right_comm, Nat.add_assoc]
          simp only [shift]

omit [SampleableType F] [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [AddCommGroup G₂]
  [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem mapIdx_sum_mul_left {β : Type} (a : F) (f : Nat → β → F) (l : List β) :
    (l.mapIdx fun n b => a * f n b).sum = a * (l.mapIdx f).sum := by
  simp only [List.mapIdx_eq_ofFn, List.sum_ofFn, Finset.mul_sum]

omit [SampleableType F] [Fintype F] [DecidableEq F] [Fintype Period] [DecidableEq Period] [SampleableType G₁]
  [Fintype G₁] [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]
  [DecidableEq Gₜ] in
theorem signSum₁ : signSum w.2 (correction₁ y) w.1.1.ξ w.1.2 0 = y * Reduction.lin' w.1.1 tr w.2 := by
  rw [signSum_eq, lin'_eq_sum, ← mapIdx_sum_mul_left]
  congr 1
  apply congrArg₂ List.mapIdx _ rfl
  funext n m
  simp only [Nat.add_zero, correction₁]
  ring

omit [SampleableType F] [Fintype F] [DecidableEq F] [Fintype Period] [DecidableEq Period] [SampleableType G₁]
  [Fintype G₁] [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]
  [DecidableEq Gₜ] in
theorem signSum₂ : signSum w.2 (correction₂ x) w.1.1.ξ w.1.2 0 = x * Reduction.lin w.1.1 tr w.2 := by
  rw [signSum_eq, lin_eq_sum, ← mapIdx_sum_mul_left]
  congr 1
  apply congrArg₂ List.mapIdx _ rfl
  funext n m
  simp only [Nat.add_zero, correction₂]
  ring

variable (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ)))
  (hsucc : succ (Gₜ := Gₜ) weight scalar g₁ g₂ (mapScalar weight scalar g₁ (syncForgery g₁ x y w, (x, y), w.2)))

omit [SampleableType F] [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [DecidableEq Gₜ] in
include hpair hsucc in
theorem sync_relation :
    x * Reduction.D w.1.1 tr w.2 + y * Reduction.D' w.1.1 tr w.2 = Reduction.K w.1.1 tr w.2 := by
  have h := relation (Gₜ := Gₜ) weight scalar g₁ g₂ hpair (syncForgery g₁ x y w, (x, y), w.2) hsucc
  simpa only [syncForgery, D_eq, D'_eq, known_eq] using h

omit [SampleableType F] [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [DecidableEq Gₜ] in
include hpair hsucc in
/-- `D ≠ 0`: scheme₁'s extraction gives `x`. -/
theorem good₁_of (hD : Reduction.D w.1.1 tr w.2 ≠ 0) :
    (dynReprA weight (forgery₁ g₁ x y w) w.2).const /
      (muW weight w.2 (forgery₁ g₁ x y w).2.mstar - (dynReprA weight (forgery₁ g₁ x y w) w.2).lin) = x := by
  have hrel := sync_relation g₁ g₂ x y w hpair hsucc
  rw [forgery₁,
    wrapped_const (correction₁ y) (final₁ y) (table g₁ w) (simSign weight (x • g₁) w.2) (syncSign g₁ x y w.2) w.1 w.2,
    wrapped_target (correction₁ y) (final₁ y) (table g₁ w) (simSign weight (x • g₁) w.2) w.1 w.2,
    wrapped_lin (correction₁ y) (final₁ y) (table g₁ w) (simSign weight (x • g₁) w.2) (syncSign g₁ x y w.2) w.1 w.2,
    signSum₁ g₁ x y w]
  change _ / Reduction.D w.1.1 tr w.2 = x
  rw [div_eq_iff hD]
  simp only [Reduction.D, Reduction.D', Reduction.K, final₁] at hrel ⊢
  linear_combination -hrel

omit [SampleableType F] [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [DecidableEq Gₜ] in
include hpair hsucc in
/-- `D' ≠ 0`: scheme₂'s extraction gives `y`. -/
theorem good₂_of (hD' : Reduction.D' w.1.1 tr w.2 ≠ 0) :
    (dynReprA (scaled weight scalar) (forgery₂ g₁ x y w) w.2).const /
      (muW (scaled weight scalar) w.2 (forgery₂ g₁ x y w).2.mstar -
        (dynReprA (scaled weight scalar) (forgery₂ g₁ x y w) w.2).lin) = y := by
  have hrel := sync_relation g₁ g₂ x y w hpair hsucc
  have hconst := wrapped_const (correction₂ x) (final₂ x) (table g₁ w)
    (simSign (scaled weight scalar) (y • g₁) w.2) (syncSign g₁ x y w.2) w.1 w.2
  rw [wrappedForgery, toForgery_const] at hconst
  rw [forgery₂, wrappedForgery, toForgery_const, hconst, ← wrappedForgery,
    wrapped_target' (correction₂ x) (final₂ x) (table g₁ w) (simSign (scaled weight scalar) (y • g₁) w.2) w.1 w.2,
    wrapped_lin' (correction₂ x) (final₂ x) (table g₁ w) (simSign (scaled weight scalar) (y • g₁) w.2)
      (syncSign g₁ x y w.2) w.1 w.2,
    signSum₂ g₁ x y w]
  change _ / Reduction.D' w.1.1 tr w.2 = y
  rw [div_eq_iff hD']
  simp only [Reduction.D, Reduction.D', Reduction.K, final₂] at hrel ⊢
  linear_combination -hrel

/-- Scheme₁'s bad branch is used when the attacked period's coefficient is nonzero. -/
def valid₁ (fo : DynForgery F (Period × F) Period) : Prop := dynDenomCoeff weight fo fo.2.mstar.1 ≠ 0

/-- Scheme₂'s bad branch is used when that coefficient vanishes; with one honest signature per
period its own coefficient is then nonzero. -/
def valid₂ (fo : DynForgery F (Period × F) Period) : Prop :=
  dynDenomCoeff weight fo fo.2.mstar.1 = 0 ∧ Proofs.valid fo

omit [SampleableType F] [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [AddCommGroup G₂]
  [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem fresh₁_iff : (forgery₁ g₁ x y w).Fresh ↔ (syncForgery g₁ x y w).rep.Fresh := by
  rw [forgery₁, wrappedForgery_fresh, syncForgery, toOffsetForgery, toForgery_fresh]
  change _ ↔ w.1.1.mstar ∉ (signatures (syncSign g₁ x y w.2) w.1.2).map Prod.fst
  rw [signatures_map_fst]

omit [SampleableType F] [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [AddCommGroup G₂]
  [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem fresh₂_iff : (forgery₂ g₁ x y w).Fresh ↔ (syncForgery g₁ x y w).rep.Fresh := by
  rw [forgery₂, wrappedForgery_fresh, syncForgery, toOffsetForgery, toForgery_fresh]
  change _ ↔ w.1.1.mstar ∉ (signatures (syncSign g₁ x y w.2) w.1.2).map Prod.fst
  rw [signatures_map_fst]

omit [SampleableType F] [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [AddCommGroup G₂]
  [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem valid₂_messages : Proofs.valid (forgery₂ g₁ x y w) ↔ Proofs.valid (syncForgery g₁ x y w).rep := by
  unfold Proofs.valid
  rw [forgery₂, wrappedForgery_messages, wrappedForgery_mstar, syncForgery, toOffsetForgery, toForgery_messages]
  change _ ↔ onePerPeriod w.1.1.mstar ((signatures (syncSign g₁ x y w.2) w.1.2).map Prod.fst)
  rw [signatures_map_fst]

omit [SampleableType F] [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [DecidableEq Gₜ] in
include hsucc in
/-- `D = 0`, `reuse ≠ 0`: scheme₁'s bad core. -/
theorem bad₁_of (hD : Reduction.D w.1.1 tr w.2 = 0) (hreuse : Reduction.reuse w.1.1 tr ≠ 0) :
    adaptiveBadCore valid₁ weight (forgery₁ g₁ x y w) w.2 := by
  refine ⟨?_, (fresh₁_iff g₁ x y w).mpr hsucc.2, ?_⟩
  · change dynDenomCoeff weight (forgery₁ g₁ x y w) w.1.1.mstar.1 ≠ 0
    rwa [forgery₁, wrapped_reuse (correction₁ y) (final₁ y) (table g₁ w) (simSign weight (x • g₁) w.2)
      (syncSign g₁ x y w.2) w.1]
  · rwa [forgery₁, wrapped_denom (correction₁ y) (final₁ y) (table g₁ w) (simSign weight (x • g₁) w.2)
      (syncSign g₁ x y w.2) w.1 w.2]

omit [SampleableType F] [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁] [DecidableEq Gₜ] in
include hsucc in
/-- `D' = 0`, `reuse = 0`: scheme₂'s bad core. -/
theorem bad₂_of (hvalid : Proofs.valid (syncForgery g₁ x y w).rep)
    (hD' : Reduction.D' w.1.1 tr w.2 = 0) (hreuse : Reduction.reuse w.1.1 tr = 0) :
    adaptiveBadCore valid₂ (scaled weight scalar) (forgery₂ g₁ x y w) w.2 := by
  refine ⟨⟨?_, (valid₂_messages g₁ x y w).mpr hvalid⟩, (fresh₂_iff g₁ x y w).mpr hsucc.2, ?_⟩
  · change dynDenomCoeff weight (forgery₂ g₁ x y w) w.1.1.mstar.1 = 0
    rwa [forgery₂, wrapped_reuse (correction₂ x) (final₂ x) (table g₁ w)
      (simSign (scaled weight scalar) (y • g₁) w.2) (syncSign g₁ x y w.2) w.1]
  · rwa [forgery₂, wrapped_denom' (correction₂ x) (final₂ x) (table g₁ w)
      (simSign (scaled weight scalar) (y • g₁) w.2) (syncSign g₁ x y w.2) w.1 w.2]

end Pointwise

omit [SampleableType F] [Fintype F] [Fintype Period] [SampleableType G₁] [Fintype G₁] [AddCommGroup G₂]
  [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem valid₂_nondegenerate (fo : DynForgery F (Period × F) Period) (hv : valid₂ fo) (hf : fo.Fresh) :
    dynDenomCoeff (scaled weight scalar) fo fo.2.mstar.1 ≠ 0 :=
  (nondegenerate fo hv.2 hf).resolve_left (not_not.mpr hv.1)

end SynchronizedPS.Wrapped
