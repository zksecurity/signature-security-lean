import Proofs.Runtime.GeneralSyncWrapMachine
import Proofs.Runtime.Extraction
import Proofs.Runtime.Weights

/-! # The general wrapper's source is the synchronized PS wrapper

Read through the bounded-randomness translation `generalSource`, the wrapper program of
`GeneralSyncWrapMachine.lean` around the attacker's realized program is `Wrapped.wrap` around the
attacker's proof view: the correction and the final hash agree request by request, and the
finishing step re-expresses the forgery's hash coefficients over the recorded marks exactly as
`remap` does over the attacker's events. The same translation carries the per-kind query bounds
of the proof view to the wrapped source and the signing bound back to the realized program. -/

open OracleComp OracleSpec Model Model.LazyAGM PFunctor
open Signatures.Runtime.WeightedAGM (GeneralRequest generalSpec generalSource)

namespace Signatures.Runtime.SyncWrapGeneral

set_option linter.unusedSectionVars false

variable {F K G₁ G₂ M : Type} [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  {randomBound : Nat}

/-! ## Marks against events -/

variable (correction : K × F → F)

/-- The mark the wrapper records for an attacker event. -/
def mark : SynchronizedPS.Wrapped.Event F K → Mark F
  | .hash _ => markHash
  | .sign m => markSign correction m

/-- `Wrapped.remap` over marks: hashes take the attacker's next hash coefficient, signatures the
next signing coefficient times the recorded correction. -/
def remapMarks (γ ξ : List F) : List (Mark F) → Nat → Nat → List F
  | [], _, _ => []
  | (false, _) :: rest, i, j => tokenCoeff γ i :: remapMarks γ ξ rest (i + 1) j
  | (true, c) :: rest, i, j => tokenCoeff ξ j * c :: remapMarks γ ξ rest i (j + 1)

theorem remap_eq_remapMarks (γ ξ : List F) (events : List (SynchronizedPS.Wrapped.Event F K)) (i j : Nat) :
    SynchronizedPS.Wrapped.remap correction γ ξ events i j =
      remapMarks γ ξ (events.map (mark correction)) i j := by
  induction events generalizing i j with
  | nil => rfl
  | cons event rest ih =>
    cases event <;> simp [SynchronizedPS.Wrapped.remap, remapMarks, mark, markHash, markSign, ih]

/-! ## The realized output and its finishing step -/

/-- The attacker's realized output: period/message pair, aggregate coefficient and the two
coefficient lists, as the weighted pipeline encodes them. -/
abbrev OutTy := AGM.outputTy Weights.syncMessage

/-- A single-signer forgery reported with no co-signers. -/
def embed (out : Output F (K × F)) : Output F (SynchronizedPS.Forgery F K) :=
  ⟨(out.mstar, []), out.β, out.γ, out.ξ⟩

/-- A mark as the first-order language types it: the signing flag and the recorded correction. -/
abbrev markTy : Ty CryptoAtom := .pair .bool scalar

variable (F G₁ G₂ K M) in
/-- The realized output as the proof-side output record. -/
def decode (out : OutTy.Value (cryptoBase F G₁ G₂ K M)) : Output F (K × F) := AGM.outputView out

variable (finalFn : K × F → F)

/-- Finish: keep the forgery, re-express the hash coefficients over the marks (recorded newest
first) and subtract the final hash's scalar. -/
def fin (result : OutTy.Value (cryptoBase F G₁ G₂ K M)) (marks : List (Mark F)) :
    OutTy.Value (cryptoBase F G₁ G₂ K M) :=
  (result.1, (result.2.1, (remapMarks result.2.2.1 result.2.2.2 marks.reverse 0 0 ++ [-(finalFn result.1)], result.2.2.2)))

/-- The attacked period. -/
def finalIndex (result : OutTy.Value (cryptoBase F G₁ G₂ K M)) : K := result.1.1

theorem decode_fin (result : OutTy.Value (cryptoBase F G₁ G₂ K M)) (marks : List (Mark F)) :
    decode F K G₁ G₂ M (fin finalFn result marks) =
      ⟨result.1, result.2.1, remapMarks result.2.2.1 result.2.2.2 marks.reverse 0 0 ++ [-(finalFn result.1)], result.2.2.2⟩ := rfl

/-! ## Reading the general interface as the lazy AGM interface -/

/-- The request relabelling performed by `generalSource`. -/
def rename : GeneralRequest K (K × F) randomBound → (ℕ ⊕ K) ⊕ (K × F)
  | .inl (.inl n) => .inl (.inl n.val)
  | .inl (.inr t) => .inl (.inr t)
  | .inr m => .inr m

variable {In : Type}

theorem simulateQ_generalSource_random (n : Fin (randomBound + 1))
    (k : (Spec F K G₁ randomBound).Range (.inl (.inl n)) → OracleComp (Spec F K G₁ randomBound) In) :
    simulateQ (generalSource randomBound) (OracleComp.queryBind (spec := Spec F K G₁ randomBound) (.inl (.inl n)) k) =
      OracleComp.queryBind (spec := advSpec K (K × F) G₁) (.inl (.inl n.val))
        fun x => simulateQ (generalSource randomBound) (k x) := by
  change simulateQ (generalSource randomBound) (liftM ((Spec F K G₁ randomBound).query (.inl (.inl n))) >>= k) = _
  rw [simulateQ_bind, simulateQ_spec_query]
  rfl

theorem simulateQ_generalSource_hash (t : K)
    (k : (Spec F K G₁ randomBound).Range (.inl (.inr t)) → OracleComp (Spec F K G₁ randomBound) In) :
    simulateQ (generalSource randomBound) (OracleComp.queryBind (spec := Spec F K G₁ randomBound) (.inl (.inr t)) k) =
      OracleComp.queryBind (spec := advSpec K (K × F) G₁) (.inl (.inr t))
        fun x => simulateQ (generalSource randomBound) (k x) := by
  change simulateQ (generalSource randomBound) (liftM ((Spec F K G₁ randomBound).query (.inl (.inr t))) >>= k) = _
  rw [simulateQ_bind, simulateQ_spec_query]
  rfl

theorem simulateQ_generalSource_sign (m : K × F)
    (k : (Spec F K G₁ randomBound).Range (.inr m) → OracleComp (Spec F K G₁ randomBound) In) :
    simulateQ (generalSource randomBound) (OracleComp.queryBind (spec := Spec F K G₁ randomBound) (.inr m) k) =
      OracleComp.queryBind (spec := advSpec K (K × F) G₁) (.inr m)
        fun x => simulateQ (generalSource randomBound) (k x) := by
  change simulateQ (generalSource randomBound) (liftM ((Spec F K G₁ randomBound).query (.inr m)) >>= k) = _
  rw [simulateQ_bind, simulateQ_spec_query]
  rfl

theorem map_queryBind {ι : Type} {spec : OracleSpec ι} {α β : Type} (f : α → β) (t : ι)
    (k : spec.Range t → OracleComp spec α) :
    f <$> OracleComp.queryBind t k = OracleComp.queryBind t fun x => f <$> k x := rfl

/-- A per-kind query bound on the relabelled program is one on the program. -/
theorem isQueryBoundP_of_simulateQ_generalSource (P : OracleComp (Spec F K G₁ randomBound) In)
    (p : (ℕ ⊕ K) ⊕ (K × F) → Prop) [DecidablePred p] (n : ℕ)
    (h : IsQueryBoundP (simulateQ (generalSource randomBound) P) p n) :
    IsQueryBoundP P (fun i => p (rename i)) n := by
  induction P generalizing n with
  | pure result => exact isQueryBoundP_pure _ _ _
  | queryBind t k ih =>
    rw [isQueryBoundP_queryBind_iff]
    rcases t with (r | t) | m
    · rw [simulateQ_generalSource_random, isQueryBoundP_queryBind_iff] at h
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩
    · rw [simulateQ_generalSource_hash, isQueryBoundP_queryBind_iff] at h
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩
    · rw [simulateQ_generalSource_sign, isQueryBoundP_queryBind_iff] at h
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

/-! ## The general wrapper is the lazy AGM wrapper -/

variable {Out In' Out' U : Type} (fin' : In → List (Mark F) → Out) (finalIndex' : In → K)

/-- Through `generalSource`, translating the realized program is `Wrapped.translate` of the
relabelled program, with the finish read on marks. -/
theorem map_simulateQ_translate (g : In → In') (h : Out → Out')
    (fI : In' → K) (hfI : ∀ r, fI (g r) = finalIndex' r)
    (finish : U → In' → List (SynchronizedPS.Wrapped.Event F K) → Out') (u : U)
    (hfin : ∀ r events, finish u (g r) events = h (fin' r (events.map (mark correction)).reverse))
    (P : OracleComp (Spec F K G₁ randomBound) In) (events : List (SynchronizedPS.Wrapped.Event F K)) :
    h <$> simulateQ (generalSource randomBound)
        (translate correction finalIndex' fin' P (events.map (mark correction)).reverse) =
      SynchronizedPS.Wrapped.translate fI (fun _ => correction) finish u
        (g <$> simulateQ (generalSource randomBound) P) events := by
  induction P generalizing events with
  | pure result =>
    show h <$> simulateQ (generalSource randomBound)
        (translate correction finalIndex' fin' (pure result) (events.map (mark correction)).reverse) =
      SynchronizedPS.Wrapped.translate fI (fun _ => correction) finish u
        (g <$> simulateQ (generalSource randomBound) (pure result)) events
    rw [translate_pure, simulateQ_generalSource_hash, map_queryBind]
    simp only [simulateQ_pure, map_pure]
    rw [SynchronizedPS.Wrapped.translate_pure, hfI, hfin]
  | queryBind t k ih =>
    rcases t with (n | t) | m
    · rw [translate_random, simulateQ_generalSource_random, simulateQ_generalSource_random, map_queryBind,
        map_queryBind, SynchronizedPS.Wrapped.translate_random]
      exact congrArg (OracleComp.queryBind _) (funext fun x => ih x events)
    · rw [translate_hash, simulateQ_generalSource_hash, simulateQ_generalSource_hash, map_queryBind,
        map_queryBind, SynchronizedPS.Wrapped.translate_hash]
      refine congrArg (OracleComp.queryBind _) (funext fun x => ?_)
      have := ih x (events ++ [.hash t])
      rwa [List.map_append, List.map_singleton, List.reverse_append, List.reverse_singleton,
        List.singleton_append] at this
    · rw [translate_sign, simulateQ_generalSource_hash, simulateQ_generalSource_sign, map_queryBind,
        map_queryBind, SynchronizedPS.Wrapped.translate_sign]
      refine congrArg (OracleComp.queryBind _) (funext fun point => ?_)
      rw [simulateQ_generalSource_sign, map_queryBind]
      refine congrArg (OracleComp.queryBind _) (funext fun σ => ?_)
      have := ih (σ + correction m • point) (events ++ [.sign m])
      rwa [List.map_append, List.map_singleton, List.reverse_append, List.reverse_singleton,
        List.singleton_append] at this

/-- **The wrapped realized program is the wrapped attacker.** At every weighted public key, the
general wrapper around the attacker's realized program, read through `generalSource` and the
output encoding, is `Wrapped.wrap` around its proof view. -/
theorem decode_translate_eq_wrap
    (program : G₂ × G₂ → OracleComp (Spec F K G₁ randomBound) (OutTy.Value (cryptoBase F G₁ G₂ K M)))
    (V : SynchronizedPS.Proofs.View F K G₁ G₂)
    (corresponds : ∀ pk, embed <$> (decode F K G₁ G₂ M <$> simulateQ (generalSource randomBound) (program pk)) = V.main pk)
    (final : SynchronizedPS.Forgery F K → F) (hfinal : ∀ m, final (m, []) = finalFn m)
    (keys : G₂ → G₂ × G₂) (pk : G₂) :
    decode F K G₁ G₂ M <$> simulateQ (generalSource randomBound)
        (translate correction finalIndex (fin finalFn) (program (keys pk)) []) =
      (SynchronizedPS.Wrapped.wrap correction final keys V).main pk := by
  rw [SynchronizedPS.Wrapped.wrap_main, ← corresponds (keys pk), Functor.map_map]
  exact map_simulateQ_translate correction (fin finalFn) finalIndex (fun out => embed (decode F K G₁ G₂ M out))
    (decode F K G₁ G₂ M) (fun result => result.mstar.1.1) (fun _ => rfl) _ pk
    (fun r events => by
      simp only [embed, decode, AGM.outputView, fin, hfinal, remap_eq_remapMarks, List.reverse_reverse])
    (program (keys pk)) []

/-! ## Query bounds of the wrapped attacker -/

variable (kind : (ℕ ⊕ K) ⊕ (K × F) → Fin 3)
  (hk0 : ∀ n, kind (.inl (.inl n)) = 0) (hk1 : ∀ t, kind (.inl (.inr t)) = 1) (hk2 : ∀ m, kind (.inr m) = 2)
  {In Out U : Type} (fI : In → K) (c : U → K × F → F)
  (finish : U → In → List (SynchronizedPS.Wrapped.Event F K) → Out) (u : U)

include hk0 hk1 hk2

theorem wrapped_random_bound (P : OracleComp (advSpec K (K × F) G₁) In)
    (events : List (SynchronizedPS.Wrapped.Event F K)) (n : ℕ)
    (hn : IsQueryBoundP P (fun i => kind i = 0) n) :
    IsQueryBoundP (SynchronizedPS.Wrapped.translate fI c finish u P events) (fun i => kind i = 0) n := by
  induction P generalizing events n with
  | pure result =>
    show IsQueryBoundP (SynchronizedPS.Wrapped.translate fI c finish u (pure result) events) _ _
    rw [SynchronizedPS.Wrapped.translate_pure, isQueryBoundP_queryBind_iff]
    exact ⟨Or.inl (by simp [hk1]), fun _ => by simp [hk1]⟩
  | queryBind t k ih =>
    rw [isQueryBoundP_queryBind_iff] at hn
    rcases t with (r | t) | m
    · rw [SynchronizedPS.Wrapped.translate_random, isQueryBoundP_queryBind_iff]
      exact ⟨hn.1, fun x => ih x events _ (hn.2 x)⟩
    · rw [SynchronizedPS.Wrapped.translate_hash, isQueryBoundP_queryBind_iff]
      refine ⟨Or.inl (by simp [hk1]), fun x => ?_⟩
      simp only [hk1, Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false]
      exact ih x _ _ (by simpa [hk1] using hn.2 x)
    · rw [SynchronizedPS.Wrapped.translate_sign, isQueryBoundP_queryBind_iff]
      refine ⟨Or.inl (by simp [hk1]), fun x => ?_⟩
      simp only [hk1, Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false]
      rw [isQueryBoundP_queryBind_iff]
      refine ⟨Or.inl (by simp [hk2]), fun σ => ?_⟩
      simp only [hk2, Fin.isValue, Fin.reduceEq, ite_false]
      exact ih _ _ _ (by simpa [hk2] using hn.2 _)

theorem wrapped_sign_bound (P : OracleComp (advSpec K (K × F) G₁) In)
    (events : List (SynchronizedPS.Wrapped.Event F K)) (n : ℕ)
    (hn : IsQueryBoundP P (fun i => kind i = 2) n) :
    IsQueryBoundP (SynchronizedPS.Wrapped.translate fI c finish u P events) (fun i => kind i = 2) n := by
  induction P generalizing events n with
  | pure result =>
    show IsQueryBoundP (SynchronizedPS.Wrapped.translate fI c finish u (pure result) events) _ _
    rw [SynchronizedPS.Wrapped.translate_pure, isQueryBoundP_queryBind_iff]
    exact ⟨Or.inl (by simp [hk1]), fun _ => by simp [hk1]⟩
  | queryBind t k ih =>
    rw [isQueryBoundP_queryBind_iff] at hn
    rcases t with (r | t) | m
    · rw [SynchronizedPS.Wrapped.translate_random, isQueryBoundP_queryBind_iff]
      refine ⟨Or.inl (by simp [hk0]), fun x => ?_⟩
      simp only [hk0, Fin.isValue, Fin.reduceEq, ite_false]
      exact ih x events _ (by simpa [hk0] using hn.2 x)
    · rw [SynchronizedPS.Wrapped.translate_hash, isQueryBoundP_queryBind_iff]
      refine ⟨Or.inl (by simp [hk1]), fun x => ?_⟩
      simp only [hk1, Fin.isValue, Fin.reduceEq, ite_false]
      exact ih x _ _ (by simpa [hk1] using hn.2 x)
    · rw [SynchronizedPS.Wrapped.translate_sign, isQueryBoundP_queryBind_iff]
      refine ⟨Or.inl (by simp [hk1]), fun x => ?_⟩
      simp only [hk1, Fin.isValue, Fin.reduceEq, ite_false]
      rw [isQueryBoundP_queryBind_iff]
      exact ⟨hn.1, fun σ => ih _ _ _ (hn.2 _)⟩

/-- Hash requests of the wrapper: the attacker's, one per signing request, and the final one. -/
theorem wrapped_hash_bound (P : OracleComp (advSpec K (K × F) G₁) In)
    (events : List (SynchronizedPS.Wrapped.Event F K)) (hashes signs : ℕ)
    (hh : IsQueryBoundP P (fun i => kind i = 1) hashes) (hs : IsQueryBoundP P (fun i => kind i = 2) signs) :
    IsQueryBoundP (SynchronizedPS.Wrapped.translate fI c finish u P events) (fun i => kind i = 1)
      (hashes + signs + 1) := by
  induction P generalizing events hashes signs with
  | pure result =>
    show IsQueryBoundP (SynchronizedPS.Wrapped.translate fI c finish u (pure result) events) _ _
    rw [SynchronizedPS.Wrapped.translate_pure, isQueryBoundP_queryBind_iff]
    exact ⟨Or.inr (by omega), fun _ => by simp⟩
  | queryBind t k ih =>
    rw [isQueryBoundP_queryBind_iff] at hh hs
    rcases t with (r | t) | m
    · rw [SynchronizedPS.Wrapped.translate_random, isQueryBoundP_queryBind_iff]
      refine ⟨Or.inl (by simp [hk0]), fun x => ?_⟩
      simp only [hk0, Fin.isValue, Fin.reduceEq, ite_false]
      exact ih x events hashes signs (by simpa [hk0] using hh.2 x) (by simpa [hk0] using hs.2 x)
    · have hpos : 0 < hashes := by simpa [hk1] using hh.1
      rw [SynchronizedPS.Wrapped.translate_hash, isQueryBoundP_queryBind_iff]
      refine ⟨Or.inr (by omega), fun x => ?_⟩
      simp only [hk1, ite_true]
      exact (ih x _ (hashes - 1) signs (by simpa [hk1] using hh.2 x) (by simpa [hk1] using hs.2 x)).mono
        (by omega)
    · have hpos : 0 < signs := by simpa [hk2] using hs.1
      rw [SynchronizedPS.Wrapped.translate_sign, isQueryBoundP_queryBind_iff]
      refine ⟨Or.inr (by omega), fun x => ?_⟩
      simp only [hk1, ite_true]
      rw [isQueryBoundP_queryBind_iff]
      refine ⟨Or.inl (by simp [hk2]), fun σ => ?_⟩
      simp only [hk2, Fin.isValue, Fin.reduceEq, ite_false]
      exact (ih _ _ hashes (signs - 1) (by simpa [hk2] using hh.2 _) (by simpa [hk2] using hs.2 _)).mono
        (by omega)

end Signatures.Runtime.SyncWrapGeneral
