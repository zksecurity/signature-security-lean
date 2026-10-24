import Proofs.LinearFunctional.LazyAGMTransport
import Proofs.Model.FiniteDomain

/-! Finite proof presentations for labelled weighted attackers. A label can be
an OOPS topic or a Proximity slot. Covers include every adaptive request and
final output over generated keys; neither their construction nor their size is
part of the executable reduction. -/

open OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.MessageTransport (mapOutput)

namespace Model.LazyAGM.WeightedTransport

variable {F ι κ M N T G₁ G₂ : Type}

def LabelCovered (indexLabel : ι → T) (messageLabel : M → T) (cover : Finset T)
    (oa : OracleComp (advSpec ι M G₁) (Output F M)) : Prop :=
  allPathsSatisfy
    (fun q => match q with
      | .inl (.inl _) => True
      | .inl (.inr i) => indexLabel i ∈ cover
      | .inr m => messageLabel m ∈ cover)
    (fun out => messageLabel out.mstar ∈ cover) (fun _ => Set.univ) oa

theorem exists_label_cover {K : Type} [Finite K] [Finite G₁]
    (indexLabel : ι → T) (messageLabel : M → T)
    (oa : K → OracleComp (advSpec ι M G₁) (Output F M)) :
    ∃ cover : Finset T, ∀ k, LabelCovered indexLabel messageLabel cover (oa k) := by
  classical
  let labels : (advSpec ι M G₁).Domain → Finset T := fun q => match q with
    | .inl (.inl _) => ∅
    | .inl (.inr i) => {indexLabel i}
    | .inr m => {messageLabel m}
  have : ∀ q, Finite ((advSpec ι M G₁).Range q) := by
    intro q
    rcases q with ((n | i) | m)
    · exact inferInstanceAs (Finite (Fin (n + 1)))
    · exact inferInstanceAs (Finite G₁)
    · exact inferInstanceAs (Finite G₁)
  obtain ⟨cover, hcover⟩ := Signatures.FiniteDomain.exists_family_cover labels
    (fun out => {messageLabel out.mstar}) oa
  refine ⟨cover, fun k => ?_⟩
  apply Signatures.FiniteDomain.allPaths_mono (oa k) _ _ (hcover k)
  · intro q hq
    rcases q with ((n | i) | m)
    · trivial
    · exact hq (Finset.mem_singleton_self _)
    · exact hq (Finset.mem_singleton_self _)
  · intro out hout
    exact hout (Finset.mem_singleton_self _)

/-- Every requested index/message and final target has a preimage in the
chosen proof presentation. Random requests and algebraic coefficients are unchanged. -/
def Liftable (index : κ → ι) (message : N → M)
    (oa : OracleComp (advSpec ι M G₁) (Output F M)) : Prop :=
  allPathsSatisfy
    (fun q => match q with
      | .inl (.inl _) => True
      | .inl (.inr i) => i ∈ Set.range index
      | .inr m => m ∈ Set.range message)
    (fun out => out.mstar ∈ Set.range message) (fun _ => Set.univ) oa

theorem LabelCovered.liftable (indexLabel : ι → T) (messageLabel : M → T)
    (cover : Finset T) (index : κ → ι) (message : N → M)
    (hi : ∀ i, indexLabel i ∈ cover → i ∈ Set.range index)
    (hm : ∀ m, messageLabel m ∈ cover → m ∈ Set.range message)
    (oa : OracleComp (advSpec ι M G₁) (Output F M))
    (h : LabelCovered indexLabel messageLabel cover oa) : Liftable index message oa := by
  apply Signatures.FiniteDomain.allPaths_mono oa _ _ h
  · intro q hq
    rcases q with ((n | i) | m)
    · trivial
    · exact hi i hq
    · exact hm m hq
  · intro out hout
    exact hm out.mstar hout

noncomputable def restrictMain (index : κ → ι) (message : N → M)
    (oa : OracleComp (advSpec ι M G₁) (Output F M)) (h : Liftable index message oa) :
    OracleComp (advSpec κ N G₁) (Output F N) := by
  induction oa using OracleComp.recOn with
  | pure out =>
      have hout : out.mstar ∈ Set.range message := (allPathsSatisfy_pure out).mp h
      exact pure ⟨Classical.choose hout, out.β, out.γ, out.ξ⟩
  | queryBind q next ih =>
      have hq := ((allPathsSatisfy_query_bind q next).mp h).1
      have hn := ((allPathsSatisfy_query_bind q next).mp h).2
      rcases q with ((n | i) | m)
      · exact query (spec := advSpec κ N G₁) (.inl (.inl n)) >>=
          fun r => ih r (hn r (Set.mem_univ _))
      · exact query (spec := advSpec κ N G₁) (.inl (.inr (Classical.choose hq))) >>=
          fun r => ih r (hn r (Set.mem_univ _))
      · exact query (spec := advSpec κ N G₁) (.inr (Classical.choose hq)) >>=
          fun r => ih r (hn r (Set.mem_univ _))

theorem restrictMain_random (index : κ → ι) (message : N → M) (n : Nat)
    (next : Fin (n + 1) → OracleComp (advSpec ι M G₁) (Output F M))
    (h : Liftable index message (OracleComp.queryBind (spec := advSpec ι M G₁) (.inl (.inl n)) next)) :
    restrictMain index message (OracleComp.queryBind (spec := advSpec ι M G₁) (.inl (.inl n)) next) h =
      (query (spec := advSpec κ N G₁) (.inl (.inl n)) >>= fun r =>
        restrictMain index message (next r)
          (((allPathsSatisfy_query_bind (spec := advSpec ι M G₁) (.inl (.inl n)) next).mp h).2 r (Set.mem_univ _))) := rfl

theorem restrictMain_hash (index : κ → ι) (message : N → M) (i : ι)
    (next : G₁ → OracleComp (advSpec ι M G₁) (Output F M))
    (h : Liftable index message (OracleComp.queryBind (spec := advSpec ι M G₁) (.inl (.inr i)) next)) :
    restrictMain index message (OracleComp.queryBind (spec := advSpec ι M G₁) (.inl (.inr i)) next) h =
      (query (spec := advSpec κ N G₁) (.inl (.inr (Classical.choose
        (((allPathsSatisfy_query_bind (spec := advSpec ι M G₁) (.inl (.inr i)) next).mp h).1)))) >>= fun r =>
        restrictMain index message (next r)
          (((allPathsSatisfy_query_bind (spec := advSpec ι M G₁) (.inl (.inr i)) next).mp h).2 r (Set.mem_univ _))) := rfl

theorem restrictMain_sign (index : κ → ι) (message : N → M) (m : M)
    (next : G₁ → OracleComp (advSpec ι M G₁) (Output F M))
    (h : Liftable index message (OracleComp.queryBind (spec := advSpec ι M G₁) (.inr m) next)) :
    restrictMain index message (OracleComp.queryBind (spec := advSpec ι M G₁) (.inr m) next) h =
      (query (spec := advSpec κ N G₁) (.inr (Classical.choose
        (((allPathsSatisfy_query_bind (spec := advSpec ι M G₁) (.inr m) next).mp h).1))) >>= fun r =>
        restrictMain index message (next r)
          (((allPathsSatisfy_query_bind (spec := advSpec ι M G₁) (.inr m) next).mp h).2 r (Set.mem_univ _))) := rfl

theorem mapMain_restrictMain (index : κ → ι) (message : N → M)
    (oa : OracleComp (advSpec ι M G₁) (Output F M)) (h : Liftable index message oa) :
    mapMain index message (restrictMain index message oa h) = oa := by
  induction oa using OracleComp.recOn with
  | pure out =>
      change pure (mapOutput message ⟨Classical.choose _, out.β, out.γ, out.ξ⟩) =
        (pure out : OracleComp (advSpec ι M G₁) (Output F M))
      have he := Classical.choose_spec ((allPathsSatisfy_pure out).mp h)
      simp only [mapOutput, he]
  | queryBind q next ih =>
      have hq := ((allPathsSatisfy_query_bind q next).mp h).1
      rcases q with ((n | i) | m) <;>
        simp only [restrictMain_random, restrictMain_hash, restrictMain_sign, mapMain_query_bind, queries]
      · apply congrArg (fun k => query _ >>= k)
        funext r
        exact ih r _
      · rw [Classical.choose_spec hq]
        apply congrArg (fun k => query _ >>= k)
        funext r
        exact ih r _
      · rw [Classical.choose_spec hq]
        apply congrArg (fun k => query _ >>= k)
        funext r
        exact ih r _

/-- Values at ungenerated public keys use a covered default. Equality is
required only on the actual generated-key family, which can be finite even if G₂ is not. -/
noncomputable def restrictPublicKeys (index : κ → ι) (message : N → M)
    (A : Adversary F ι M G₁ G₂) (defaultKey : G₂)
    (hdefault : Liftable index message (A.main defaultKey)) : Adversary F κ N G₁ G₂ := by
  classical
  exact ⟨fun pk => if h : Liftable index message (A.main pk) then restrictMain index message (A.main pk) h
    else restrictMain index message (A.main defaultKey) hdefault⟩

theorem restrictPublicKeys_map_at (index : κ → ι) (message : N → M)
    (A : Adversary F ι M G₁ G₂) (defaultKey : G₂)
    (hdefault : Liftable index message (A.main defaultKey)) (pk : G₂)
    (hpk : Liftable index message (A.main pk)) :
    (mapAdversary index message (restrictPublicKeys index message A defaultKey hdefault)).main pk =
      A.main pk := by
  simp only [mapAdversary, restrictPublicKeys, dite_eq_left hpk, mapMain_restrictMain]

end Model.LazyAGM.WeightedTransport
