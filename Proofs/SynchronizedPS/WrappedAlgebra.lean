import Proofs.SynchronizedPS.Wrapped

/-! The weighted-scheme quantities of a wrapped forgery, in terms of the synchronized PS ones.
Both weighted schemes keep the attacker's signing coefficients and messages, so their `lin`,
denominators and coordinate functionals are the synchronized `lin`, `lin'`, `D`, `D'` and
`reuse`; the wrapper's hash coefficients turn the constant into `const + Σ ξ_j·c(m_j)·ρ(t_j) −
final·ρ(t*)`, which is `K − y·D'` for scheme₁ and `K − x·D` for scheme₂. -/

open BilinearGroup OracleComp AlgebraicGroupModel AlgebraicGroupModel.LinFunctional
open Model Model.LazyAGM Model.LazyAGM.Proofs SynchronizedPS.Proofs

namespace SynchronizedPS.Wrapped

variable {F Period G₁ : Type} [Field F] [DecidableEq Period] [AddCommGroup G₁] [Module F G₁]

/-- The messages the attacker had signed, in order. -/
def messages : List (Event F Period) → List (Period × F)
  | [] => []
  | .hash _ :: rest => messages rest
  | .sign m :: rest => m :: messages rest

omit [Field F] [DecidableEq Period] [AddCommGroup G₁] [Module F G₁] in
theorem signatures_map_fst (sign : Period × F → G₁) (events : List (Event F Period)) :
    (signatures sign events).map Prod.fst = messages events := by
  induction events with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [signatures, messages, ih]

omit [Field F] [DecidableEq Period] [AddCommGroup G₁] [Module F G₁] in
theorem signatures_eq_map (sign : Period × F → G₁) (events : List (Event F Period)) :
    signatures sign events = (messages events).map fun m => (m, sign m) := by
  induction events with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [signatures, messages, ih]

omit [Field F] [DecidableEq Period] [AddCommGroup G₁] [Module F G₁] in
theorem mapIdx_map {α β γ : Type} (f : Nat → β → γ) (g : α → β) (l : List α) :
    (l.map g).mapIdx f = l.mapIdx fun n a => f n (g a) := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.mapIdx_cons, ih]

/-! ## Coefficient lists -/

omit [DecidableEq Period] [AddCommGroup G₁] [Module F G₁] in
theorem tokenCoeff_cons_succ (a : F) (c : List F) (n : Nat) : tokenCoeff (a :: c) (n + 1) = tokenCoeff c n := by
  simp [tokenCoeff]

omit [DecidableEq Period] [AddCommGroup G₁] [Module F G₁] in
theorem tokenCoeff_append_left (c d : List F) (n : Nat) (h : n < c.length) :
    tokenCoeff (c ++ d) n = tokenCoeff c n := by
  simp [tokenCoeff, List.getElem?_append_left h]

omit [DecidableEq Period] [AddCommGroup G₁] [Module F G₁] in
theorem tokenCoeff_append_length (c : List F) (e : F) : tokenCoeff (c ++ [e]) c.length = e := by
  simp [tokenCoeff]

omit [DecidableEq Period] [AddCommGroup G₁] [Module F G₁] in
theorem mapIdx_tokenCoeff_append {β : Type} (g : β → F) (c d : List F) (l : List β)
    (h : l.length ≤ c.length) :
    (l.mapIdx fun n p => tokenCoeff (c ++ d) n * g p) = l.mapIdx fun n p => tokenCoeff c n * g p := by
  apply List.ext_getElem
  · simp
  · intro n hn _
    simp only [List.getElem_mapIdx]
    rw [tokenCoeff_append_left]
    simp only [List.length_mapIdx] at hn
    omega

omit [DecidableEq Period] [AddCommGroup G₁] [Module F G₁] in
theorem mapIdx_tokenCoeff_eq_zipWith {β : Type} (g : β → F) :
    ∀ (c : List F) (l : List β), c.length = l.length →
      (l.mapIdx fun n p => tokenCoeff c n * g p).sum = (List.zipWith (fun coeff p => coeff * g p) c l).sum
  | [], [], _ => by simp
  | a :: c, p :: l, h => by
      simp only [List.mapIdx_cons, List.zipWith_cons_cons, List.sum_cons]
      have head : tokenCoeff (a :: c) 0 = a := by simp [tokenCoeff]
      have tail : (l.mapIdx fun n q => tokenCoeff (a :: c) (n + 1) * g q) =
          l.mapIdx fun n q => tokenCoeff c n * g q := rfl
      rw [head, tail, mapIdx_tokenCoeff_eq_zipWith g c l (by simpa using h)]

/-! ## Sums over the ordered events -/

section Sums
variable (ρ : Period → F)

/-- `Σ tokenCoeff γ (i + k) · ρ(t_k)` over the attacker's own hashes. -/
def ownSum (γ : List F) : List (Event F Period) → Nat → F
  | [], _ => 0
  | .hash t :: rest, i => tokenCoeff γ i * ρ t + ownSum γ rest (i + 1)
  | .sign _ :: rest, i => ownSum γ rest i

/-- `Σ tokenCoeff ξ (j + k) · c(m_k) · ρ(t_k)` over the signing queries. -/
def signSum (correction : Period × F → F) (ξ : List F) : List (Event F Period) → Nat → F
  | [], _ => 0
  | .hash _ :: rest, j => signSum correction ξ rest j
  | .sign m :: rest, j => tokenCoeff ξ j * correction m * ρ m.1 + signSum correction ξ rest (j + 1)

omit [DecidableEq Period] [AddCommGroup G₁] [Module F G₁] in
theorem hashes_sum (H : Period → G₁) (γ : List F) (events : List (Event F Period)) (i : Nat) :
    ((hashes H events).mapIdx fun n p => tokenCoeff γ (n + i) * ρ p.1).sum = ownSum ρ γ events i := by
  induction events generalizing i with
  | nil => rfl
  | cons event rest ih =>
      cases event with
      | hash t =>
          simp only [hashes, List.mapIdx_cons, List.sum_cons, ownSum, zero_add]
          rw [← ih (i + 1)]
          have shift : ∀ n (p : Period × G₁), tokenCoeff γ (n + 1 + i) * ρ p.1 =
              tokenCoeff γ (n + (i + 1)) * ρ p.1 := fun n p => by rw [Nat.add_right_comm, Nat.add_assoc]
          simp only [shift]
      | sign m => simp only [hashes, ownSum, ih]

omit [DecidableEq Period] [AddCommGroup G₁] [Module F G₁] in
theorem wrappedHashes_sum (H : Period → G₁) (correction : Period × F → F) (γ ξ : List F)
    (events : List (Event F Period)) (i j : Nat) :
    (List.zipWith (fun coeff (p : Period × G₁) => coeff * ρ p.1)
        (remap correction γ ξ events i j) (wrappedHashes H events)).sum =
      ownSum ρ γ events i + signSum ρ correction ξ events j := by
  induction events generalizing i j with
  | nil => simp [remap, wrappedHashes, ownSum, signSum]
  | cons event rest ih =>
      cases event with
      | hash t =>
          simp only [remap, wrappedHashes, List.zipWith_cons_cons, List.sum_cons, ownSum, signSum, ih]
          ring
      | sign m =>
          simp only [remap, wrappedHashes, List.zipWith_cons_cons, List.sum_cons, ownSum, signSum, ih]
          ring

omit [DecidableEq Period] [AddCommGroup G₁] [Module F G₁] in
theorem remap_length (correction : Period × F → F) (γ ξ : List F) (events : List (Event F Period)) (i j : Nat) :
    (remap correction γ ξ events i j).length = events.length := by
  induction events generalizing i j with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [remap, ih]

omit [Field F] [DecidableEq Period] [AddCommGroup G₁] [Module F G₁] in
theorem wrappedHashes_length (H : Period → G₁) (events : List (Event F Period)) :
    (wrappedHashes H events).length = events.length := by
  induction events with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [wrappedHashes, ih]

end Sums

/-! ## Scheme quantities of the wrapped forgery -/

variable (correction : Period × F → F) (final : Forgery F Period → F) (H : Period → G₁)
  (signO sign : Period × F → G₁) (z : Output F (Forgery F Period) × List (Event F Period)) (ρ : Period → F)

/-- The weighted forgery the wrapper reports, as the core's representation. -/
abbrev wrappedForgery : DynForgery F (Period × F) Period :=
  toForgery (wrapped correction final H signO z)

omit [AddCommGroup G₁] [Module F G₁] in
theorem wrappedForgery_mstar : (wrappedForgery correction final H signO z).2.mstar = z.1.mstar.1 := rfl

omit [AddCommGroup G₁] [Module F G₁] in
theorem wrappedForgery_messages :
    List.ofFn (wrappedForgery correction final H signO z).2.v = messages z.2 := by
  rw [toForgery_messages]
  exact signatures_map_fst signO z.2

omit [AddCommGroup G₁] [Module F G₁] in
theorem wrappedForgery_fresh :
    (wrappedForgery correction final H signO z).Fresh ↔ z.1.mstar.1 ∉ messages z.2 := by
  rw [toForgery_fresh]
  change z.1.mstar.1 ∉ (signatures signO z.2).map Prod.fst ↔ _
  rw [signatures_map_fst]

/-! ### Generic shapes of the core's quantities on `toForgery` -/

section Generic
variable {M : Type} [Fintype Period] (w : Period → M → F) (out' : Output F M)
  (tr' : Transcript Period M G₁)

omit [AddCommGroup G₁] [Module F G₁] in
theorem toForgery_lin :
    (dynReprA w (toForgery (out', tr')) ρ).lin =
      (tr'.2.mapIdx fun n r => tokenCoeff out'.ξ n * muW w ρ r.1).sum := by
  simp only [dynReprA, reprA, toForgery, List.mapIdx_eq_ofFn, List.sum_ofFn, List.get_eq_getElem]
  rfl

omit [AddCommGroup G₁] [Module F G₁] in
theorem toForgery_const :
    (dynReprA w (toForgery (out', tr')) ρ).const = out'.β + ∑ i, baseCoeff out'.γ tr'.1 i * ρ i := rfl

omit [Fintype Period] [AddCommGroup G₁] [Module F G₁] in
theorem toForgery_coeff (i : Period) :
    dynDenomCoeff w (toForgery (out', tr')) i =
      w i out'.mstar - (tr'.2.mapIdx fun n r => tokenCoeff out'.ξ n * w i r.1).sum := by
  simp only [dynDenomCoeff, Lcoeff, toForgery, List.mapIdx_eq_ofFn, List.sum_ofFn,
    List.get_eq_getElem]
  rfl

end Generic

omit [DecidableEq Period] [AddCommGroup G₁] [Module F G₁] in
theorem lin_eq_sum : Reduction.lin z.1 (transcript H sign z.2) ρ =
    ((messages z.2).mapIdx fun n m => tokenCoeff z.1.ξ n * ρ m.1).sum := by
  simp only [Reduction.lin, transcript]
  rw [signatures_eq_map, mapIdx_map]

omit [DecidableEq Period] [AddCommGroup G₁] [Module F G₁] in
theorem lin'_eq_sum : Reduction.lin' z.1 (transcript H sign z.2) ρ =
    ((messages z.2).mapIdx fun n m => tokenCoeff z.1.ξ n * (ρ m.1 * m.2)).sum := by
  simp only [Reduction.lin', transcript]
  rw [signatures_eq_map, mapIdx_map]

omit [DecidableEq Period] [AddCommGroup G₁] [Module F G₁] in
theorem const_eq_ownSum : Reduction.const z.1 (transcript H sign z.2) ρ = z.1.β + ownSum ρ z.1.γ z.2 0 := by
  simp only [Reduction.const, transcript]
  rw [← hashes_sum ρ H z.1.γ z.2 0]
  simp

omit [AddCommGroup G₁] [Module F G₁] in
theorem reuse_eq_sum : Reduction.reuse z.1 (transcript H sign z.2) =
    1 - ((messages z.2).mapIdx fun n m => if m.1 = z.1.mstar.1.1 then tokenCoeff z.1.ξ n else 0).sum := by
  simp only [Reduction.reuse, transcript]
  rw [signatures_eq_map, mapIdx_map]

variable [Fintype Period]

theorem wrapped_lin :
    (dynReprA weight (wrappedForgery correction final H signO z) ρ).lin =
      Reduction.lin z.1 (transcript H sign z.2) ρ := by
  rw [wrappedForgery, toForgery_lin, lin_eq_sum]
  simp only [wrapped]
  rw [signatures_eq_map, mapIdx_map]
  simp only [muW_weight]

theorem wrapped_lin' :
    (dynReprA (scaled weight scalar) (wrappedForgery correction final H signO z) ρ).lin =
      Reduction.lin' z.1 (transcript H sign z.2) ρ := by
  rw [wrappedForgery, toForgery_lin, lin'_eq_sum]
  simp only [wrapped]
  rw [signatures_eq_map, mapIdx_map]
  simp only [muW_scaled, muW_weight, scalar]

/-- The constant: the attacker's, plus the corrections on the pre-sign hashes, minus the final
correction on the attacked period. -/
theorem wrapped_const :
    (dynReprA weight (wrappedForgery correction final H signO z) ρ).const =
      Reduction.const z.1 (transcript H sign z.2) ρ + signSum ρ correction z.1.ξ z.2 0 -
        final z.1.mstar * ρ z.1.mstar.1.1 := by
  rw [const_eq_ownSum, wrappedForgery, toForgery_const]
  simp only [wrapped]
  rw [baseCoeff_mul_sum, List.mapIdx_append_one, List.sum_append, List.sum_singleton,
    wrappedHashes_length, ← remap_length correction z.1.γ z.1.ξ z.2 0 0, tokenCoeff_append_length,
    mapIdx_tokenCoeff_append _ _ _ _ (by rw [remap_length, wrappedHashes_length]),
    mapIdx_tokenCoeff_eq_zipWith _ _ _ (by rw [remap_length, wrappedHashes_length]),
    wrappedHashes_sum]
  ring

omit [AddCommGroup G₁] [Module F G₁] in
theorem wrapped_target : muW weight ρ (wrappedForgery correction final H signO z).2.mstar = ρ z.1.mstar.1.1 :=
  muW_weight ρ _

omit [AddCommGroup G₁] [Module F G₁] in
theorem wrapped_target' :
    muW (scaled weight scalar) ρ (wrappedForgery correction final H signO z).2.mstar =
      ρ z.1.mstar.1.1 * z.1.mstar.1.2 := by
  rw [muW_scaled, muW_weight]
  rfl

theorem wrapped_denom :
    dynDenom weight (wrappedForgery correction final H signO z) ρ = Reduction.D z.1 (transcript H sign z.2) ρ := by
  rw [dynDenom, dynDenomCoeff, ← muW_sub_reprA_lin, Reduction.D, ← wrapped_lin correction final H signO sign]
  exact congrArg (· - _) (wrapped_target correction final H signO z ρ)

theorem wrapped_denom' :
    dynDenom (scaled weight scalar) (wrappedForgery correction final H signO z) ρ =
      Reduction.D' z.1 (transcript H sign z.2) ρ := by
  rw [dynDenom, dynDenomCoeff, ← muW_sub_reprA_lin, Reduction.D', ← wrapped_lin' correction final H signO sign]
  exact congrArg (· - _) (wrapped_target' correction final H signO z ρ)

omit [Fintype Period] in
/-- The attacked period's coordinate of the first scheme's functional is the synchronized `reuse`. -/
theorem wrapped_reuse :
    dynDenomCoeff weight (wrappedForgery correction final H signO z) z.1.mstar.1.1 =
      Reduction.reuse z.1 (transcript H sign z.2) := by
  rw [wrappedForgery, toForgery_coeff, reuse_eq_sum]
  simp only [wrapped]
  rw [signatures_eq_map, mapIdx_map]
  simp only [weight, if_true]
  congr 2
  congr 1
  funext n m
  by_cases h : m.1 = z.1.mstar.1.1 <;> simp [h, eq_comm]

end SynchronizedPS.Wrapped
