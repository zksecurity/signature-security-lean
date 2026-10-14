import Signatures.BLS.Spec.LazyAGMReduction
import Signatures.BLS.CoCDH.Proofs.FiniteMessages

/-! Finite proof presentations of arbitrary-message AGM attackers. Only the
message labels are restricted; coefficient lists and every adaptive reply path
are preserved. The possibly large cover is never an executable reduction table. -/

open OracleComp OracleSpec Model.LazyAGM

namespace BLS.LazyAGM.MessageTransport

variable {F N M G₁ G₂ : Type}

def mapOutput (f : N → M) (out : Output F N) : Output F M :=
  ⟨f out.mstar, out.β, out.γ, out.ξ⟩

def mapMain (f : N → M) (oa : OracleComp (advSpec N N G₁) (Output F N)) :
    OracleComp (advSpec M M G₁) (Output F M) :=
  mapOutput f <$> simulateQ (CoCDH.Tight.messageQueries f) oa

def mapAdversary (f : N → M) (A : Adversary F N N G₁ G₂) : Adversary F M M G₁ G₂ :=
  ⟨fun pk => mapMain f (A.main pk)⟩

theorem mapMain_query_bind (f : N → M) (q : (advSpec N N G₁).Domain)
    (next : (advSpec N N G₁).Range q → OracleComp (advSpec N N G₁) (Output F N)) :
    mapMain f (show OracleComp (advSpec N N G₁) (Output F N) from query q >>= next) =
      (CoCDH.Tight.messageQueries f q >>= fun r => mapMain f (next r) :
        OracleComp (advSpec M M G₁) (Output F M)) := by
  simp only [mapMain, simulateQ_bind, simulateQ_HasQuery_query, map_bind]

def MessageCovered (cover : Finset M) (oa : OracleComp (advSpec M M G₁) (Output F M)) : Prop :=
  allPathsSatisfy
    (fun q => match q with
      | .inl (.inl _) => True
      | .inl (.inr m) => m ∈ cover
      | .inr m => m ∈ cover)
    (fun out => out.mstar ∈ cover) (fun _ => Set.univ) oa

theorem exists_message_cover {K : Type} [Finite K] [Finite G₁]
    (oa : K → OracleComp (advSpec M M G₁) (Output F M)) :
    ∃ cover : Finset M, ∀ k, MessageCovered cover (oa k) := by
  classical
  let labels : (advSpec M M G₁).Domain → Finset M := fun q => match q with
    | .inl (.inl _) => ∅
    | .inl (.inr m) => {m}
    | .inr m => {m}
  have : ∀ q, Finite ((advSpec M M G₁).Range q) := by
    intro q
    rcases q with ((n | m) | m)
    · exact inferInstanceAs (Finite (Fin (n + 1)))
    · exact inferInstanceAs (Finite G₁)
    · exact inferInstanceAs (Finite G₁)
  obtain ⟨cover, hcover⟩ := Signatures.FiniteDomain.exists_family_cover labels (fun out => {out.mstar}) oa
  refine ⟨cover, fun k => ?_⟩
  apply Signatures.FiniteDomain.allPaths_mono (oa k) _ _ (hcover k)
  · intro q hq
    rcases q with ((n | m) | m)
    · trivial
    · exact hq (Finset.mem_singleton_self m)
    · exact hq (Finset.mem_singleton_self m)
  · intro out hout
    exact hout (Finset.mem_singleton_self out.mstar)

noncomputable def restrictMain (cover : Finset M)
    (oa : OracleComp (advSpec M M G₁) (Output F M)) (h : MessageCovered cover oa) :
    OracleComp (advSpec {m // m ∈ cover} {m // m ∈ cover} G₁) (Output F {m // m ∈ cover}) := by
  induction oa using OracleComp.recOn with
  | pure out =>
    have hout : out.mstar ∈ cover := (allPathsSatisfy_pure out).mp h
    exact pure ⟨⟨out.mstar, hout⟩, out.β, out.γ, out.ξ⟩
  | queryBind q next ih =>
    have hq := ((allPathsSatisfy_query_bind q next).mp h).1
    have hnext := ((allPathsSatisfy_query_bind q next).mp h).2
    rcases q with ((n | m) | m)
    · exact query (spec := advSpec {m // m ∈ cover} {m // m ∈ cover} G₁) (.inl (.inl n)) >>=
        fun r => ih r (hnext r (Set.mem_univ _))
    · exact query (spec := advSpec {m // m ∈ cover} {m // m ∈ cover} G₁) (.inl (.inr ⟨m, hq⟩)) >>=
        fun r => ih r (hnext r (Set.mem_univ _))
    · exact query (spec := advSpec {m // m ∈ cover} {m // m ∈ cover} G₁) (.inr ⟨m, hq⟩) >>=
        fun r => ih r (hnext r (Set.mem_univ _))

theorem restrictMain_random (cover : Finset M) (n : Nat)
    (next : Fin (n + 1) → OracleComp (advSpec M M G₁) (Output F M))
    (h : MessageCovered cover (OracleComp.queryBind (spec := advSpec M M G₁) (.inl (.inl n)) next)) :
    restrictMain cover (OracleComp.queryBind (spec := advSpec M M G₁) (.inl (.inl n)) next) h =
      (query (spec := advSpec {m // m ∈ cover} {m // m ∈ cover} G₁) (.inl (.inl n)) >>= fun r =>
        restrictMain cover (next r)
          (((allPathsSatisfy_query_bind (spec := advSpec M M G₁) (.inl (.inl n)) next).mp h).2 r (Set.mem_univ _)) :
        OracleComp (advSpec {m // m ∈ cover} {m // m ∈ cover} G₁) (Output F {m // m ∈ cover})) := rfl

theorem restrictMain_hash (cover : Finset M) (m : M)
    (next : G₁ → OracleComp (advSpec M M G₁) (Output F M))
    (h : MessageCovered cover (OracleComp.queryBind (spec := advSpec M M G₁) (.inl (.inr m)) next)) :
    restrictMain cover (OracleComp.queryBind (spec := advSpec M M G₁) (.inl (.inr m)) next) h =
      (query (spec := advSpec {m // m ∈ cover} {m // m ∈ cover} G₁)
        (.inl (.inr ⟨m, ((allPathsSatisfy_query_bind (spec := advSpec M M G₁) (.inl (.inr m)) next).mp h).1⟩)) >>= fun r =>
        restrictMain cover (next r)
          (((allPathsSatisfy_query_bind (spec := advSpec M M G₁) (.inl (.inr m)) next).mp h).2 r (Set.mem_univ _)) :
        OracleComp (advSpec {m // m ∈ cover} {m // m ∈ cover} G₁) (Output F {m // m ∈ cover})) := rfl

theorem restrictMain_sign (cover : Finset M) (m : M)
    (next : G₁ → OracleComp (advSpec M M G₁) (Output F M))
    (h : MessageCovered cover (OracleComp.queryBind (spec := advSpec M M G₁) (.inr m) next)) :
    restrictMain cover (OracleComp.queryBind (spec := advSpec M M G₁) (.inr m) next) h =
      (query (spec := advSpec {m // m ∈ cover} {m // m ∈ cover} G₁)
        (.inr ⟨m, ((allPathsSatisfy_query_bind (spec := advSpec M M G₁) (.inr m) next).mp h).1⟩) >>= fun r =>
        restrictMain cover (next r)
          (((allPathsSatisfy_query_bind (spec := advSpec M M G₁) (.inr m) next).mp h).2 r (Set.mem_univ _)) :
        OracleComp (advSpec {m // m ∈ cover} {m // m ∈ cover} G₁) (Output F {m // m ∈ cover})) := rfl

theorem mapMain_restrictMain (cover : Finset M)
    (oa : OracleComp (advSpec M M G₁) (Output F M)) (h : MessageCovered cover oa) :
    mapMain Subtype.val (restrictMain cover oa h) = oa := by
  induction oa using OracleComp.recOn with
  | pure out => rfl
  | queryBind q next ih =>
    rcases q with ((n | m) | m) <;>
      simp only [restrictMain_random, restrictMain_hash, restrictMain_sign,
        mapMain_query_bind, CoCDH.Tight.messageQueries]
    all_goals
      apply congrArg (fun k => query _ >>= k)
      funext r
      exact ih r _

noncomputable def restrictPublicKeys (cover : Finset M) (A : Adversary F M M G₁ G₂)
    (defaultKey : G₂) (hdefault : MessageCovered cover (A.main defaultKey)) :
    Adversary F {m // m ∈ cover} {m // m ∈ cover} G₁ G₂ := by
  classical
  exact ⟨fun pk => if h : MessageCovered cover (A.main pk) then restrictMain cover (A.main pk) h
    else restrictMain cover (A.main defaultKey) hdefault⟩

theorem exists_restricted_publicKeys {K : Type} [Finite K] [Nonempty K] [Finite G₁]
    (key : K → G₂) (A : Adversary F M M G₁ G₂) :
    ∃ cover : Finset M, ∃ restricted : Adversary F {m // m ∈ cover} {m // m ∈ cover} G₁ G₂,
      ∀ seed, (mapAdversary Subtype.val restricted).main (key seed) = A.main (key seed) := by
  classical
  obtain ⟨cover, hcover⟩ := exists_message_cover (fun seed => A.main (key seed))
  let seed : K := Classical.choice inferInstance
  refine ⟨cover, restrictPublicKeys cover A (key seed) (hcover seed), fun k => ?_⟩
  simp only [mapAdversary, restrictPublicKeys, dite_eq_left (hcover k), mapMain_restrictMain]

end BLS.LazyAGM.MessageTransport
