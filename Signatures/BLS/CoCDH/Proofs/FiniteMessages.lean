import Signatures.BLS.CoCDH.Spec.LazyGame
import Signatures.Model.FiniteDomain

/-! Finite proof domains for BLS attackers over arbitrary message types. Covers
include every adaptive query and final forgery, over all possible oracle replies.
They are proof artifacts, not reduction tables or efficiency bounds. -/

open OracleComp OracleSpec

namespace BLS.CoCDH.Tight

variable {M G₁ : Type}

def MessageCovered (cover : Finset M) (adv : TightAdv M G₁) : Prop :=
  allPathsSatisfy
    (fun q => match q with
      | .inl (.inl _) => True
      | .inl (.inr m) => m ∈ cover
      | .inr m => m ∈ cover)
    (fun out => out.1 ∈ cover) (fun _ => Set.univ) adv

theorem exists_message_cover {K : Type} [Finite K] [Finite G₁] (adv : K → TightAdv M G₁) :
    ∃ cover : Finset M, ∀ k, MessageCovered cover (adv k) := by
  classical
  let queryLabels : (advSpec M G₁).Domain → Finset M := fun q => match q with
    | .inl (.inl _) => ∅
    | .inl (.inr m) => {m}
    | .inr m => {m}
  have : ∀ q, Finite ((advSpec M G₁).Range q) := by
    intro q
    rcases q with ((n | m) | m)
    · change Finite (Fin (n + 1))
      infer_instance
    · exact inferInstanceAs (Finite G₁)
    · exact inferInstanceAs (Finite G₁)
  obtain ⟨cover, hcover⟩ := Signatures.FiniteDomain.exists_family_cover queryLabels (fun out => {out.1}) adv
  refine ⟨cover, fun k => ?_⟩
  apply Signatures.FiniteDomain.allPaths_mono (adv k) _ _ (hcover k)
  · intro q hq
    rcases q with ((n | m) | m)
    · trivial
    · exact hq (Finset.mem_singleton_self m)
    · exact hq (Finset.mem_singleton_self m)
  · intro out hout
    exact hout (Finset.mem_singleton_self out.1)

/-- Relabel messages while preserving private randomness and all response types. -/
def messageQueries {N : Type} (f : N → M) : QueryImpl (advSpec N G₁) (OracleComp (advSpec M G₁)) :=
  fun q => match q with
    | .inl (.inl n) => query (spec := advSpec M G₁) (.inl (.inl n))
    | .inl (.inr m) => query (spec := advSpec M G₁) (.inl (.inr (f m)))
    | .inr m => query (spec := advSpec M G₁) (.inr (f m))

def mapMessages {N : Type} (f : N → M) (adv : TightAdv N G₁) : TightAdv M G₁ :=
  (Prod.map f id <$> simulateQ (messageQueries (G₁ := G₁) f) adv : OracleComp (advSpec M G₁) (M × G₁))

theorem mapMessages_query_bind {N : Type} (f : N → M) (q : (advSpec N G₁).Domain)
    (next : (advSpec N G₁).Range q → OracleComp (advSpec N G₁) (N × G₁)) :
    mapMessages f (show OracleComp (advSpec N G₁) (N × G₁) from query q >>= next) =
      (messageQueries f q >>= fun r => mapMessages f (next r) : OracleComp (advSpec M G₁) (M × G₁)) := by
  simp only [mapMessages, simulateQ_bind, simulateQ_HasQuery_query, map_bind]

/-- Restriction uses coverage proofs to retain each message exactly. No default
message, query truncation, or rejection of an adaptive path is introduced. -/
noncomputable def restrictMessages (cover : Finset M) (adv : TightAdv M G₁)
    (h : MessageCovered cover adv) : TightAdv {m // m ∈ cover} G₁ := by
  change OracleComp (advSpec {m // m ∈ cover} G₁) ({m // m ∈ cover} × G₁)
  induction adv using OracleComp.recOn with
  | pure out =>
      have hout : out.1 ∈ cover := (allPathsSatisfy_pure out).mp h
      exact pure (⟨out.1, hout⟩, out.2)
  | queryBind q next ih =>
      have hq := ((allPathsSatisfy_query_bind q next).mp h).1
      have hnext := ((allPathsSatisfy_query_bind q next).mp h).2
      rcases q with ((n | m) | m)
      · exact query (spec := advSpec {m // m ∈ cover} G₁) (.inl (.inl n)) >>=
          fun r => ih r (hnext r (Set.mem_univ _))
      · exact query (spec := advSpec {m // m ∈ cover} G₁) (.inl (.inr ⟨m, hq⟩)) >>=
          fun r => ih r (hnext r (Set.mem_univ _))
      · exact query (spec := advSpec {m // m ∈ cover} G₁) (.inr ⟨m, hq⟩) >>=
          fun r => ih r (hnext r (Set.mem_univ _))

theorem restrictMessages_random (cover : Finset M) (n : Nat) (next : Fin (n + 1) → OracleComp (advSpec M G₁) (M × G₁))
    (h : MessageCovered cover (OracleComp.queryBind (spec := advSpec M G₁) (.inl (.inl n)) next)) :
    restrictMessages cover (OracleComp.queryBind (spec := advSpec M G₁) (.inl (.inl n)) next) h =
      (query (spec := advSpec {m // m ∈ cover} G₁) (.inl (.inl n)) >>= fun r =>
        restrictMessages cover (next r)
          (((allPathsSatisfy_query_bind (spec := advSpec M G₁) (.inl (.inl n)) next).mp h).2 r (Set.mem_univ _)) :
        OracleComp (advSpec {m // m ∈ cover} G₁) ({m // m ∈ cover} × G₁)) := rfl

theorem restrictMessages_hash (cover : Finset M) (m : M) (next : G₁ → OracleComp (advSpec M G₁) (M × G₁))
    (h : MessageCovered cover (OracleComp.queryBind (spec := advSpec M G₁) (.inl (.inr m)) next)) :
    restrictMessages cover (OracleComp.queryBind (spec := advSpec M G₁) (.inl (.inr m)) next) h =
      (query (spec := advSpec {m // m ∈ cover} G₁)
        (.inl (.inr ⟨m, ((allPathsSatisfy_query_bind (spec := advSpec M G₁) (.inl (.inr m)) next).mp h).1⟩)) >>= fun r =>
        restrictMessages cover (next r)
          (((allPathsSatisfy_query_bind (spec := advSpec M G₁) (.inl (.inr m)) next).mp h).2 r (Set.mem_univ _)) :
        OracleComp (advSpec {m // m ∈ cover} G₁) ({m // m ∈ cover} × G₁)) := rfl

theorem restrictMessages_sign (cover : Finset M) (m : M) (next : G₁ → OracleComp (advSpec M G₁) (M × G₁))
    (h : MessageCovered cover (OracleComp.queryBind (spec := advSpec M G₁) (.inr m) next)) :
    restrictMessages cover (OracleComp.queryBind (spec := advSpec M G₁) (.inr m) next) h =
      (query (spec := advSpec {m // m ∈ cover} G₁)
        (.inr ⟨m, ((allPathsSatisfy_query_bind (spec := advSpec M G₁) (.inr m) next).mp h).1⟩) >>= fun r =>
        restrictMessages cover (next r)
          (((allPathsSatisfy_query_bind (spec := advSpec M G₁) (.inr m) next).mp h).2 r (Set.mem_univ _)) :
        OracleComp (advSpec {m // m ∈ cover} G₁) ({m // m ∈ cover} × G₁)) := rfl

/-- Restricting to the finite proof domain and embedding it back gives the
original interactive program exactly, including adaptive private randomness. -/
theorem mapMessages_restrictMessages (cover : Finset M) (adv : TightAdv M G₁)
    (h : MessageCovered cover adv) :
    mapMessages Subtype.val (restrictMessages cover adv h) = adv := by
  induction adv using OracleComp.recOn with
  | pure out => rfl
  | queryBind q next ih =>
      rcases q with ((n | m) | m) <;>
        simp only [restrictMessages_random, restrictMessages_hash, restrictMessages_sign,
          mapMessages_query_bind, messageQueries]
      all_goals
        apply congrArg (fun k => query _ >>= k)
        funext r
        exact ih r _

theorem MessageCovered.cacheForgery {cover : Finset M} {adv : TightAdv M G₁}
    (h : MessageCovered cover adv) : MessageCovered cover (cacheForgery adv) := by
  unfold MessageCovered BLS.CoCDH.Tight.cacheForgery
  rw [allPathsSatisfy_bind_iff]
  apply Signatures.FiniteDomain.allPaths_mono adv (fun _ hq => hq) _ h
  intro out hout
  rw [allPathsSatisfy_query_bind]
  exact ⟨hout, fun _ _ => (allPathsSatisfy_pure out).mpr hout⟩

/-- Every finite family of attackers has an exact finite-message presentation.
Only the proof uses the possibly large union of all adaptive branches. -/
theorem exists_restricted_family {K : Type} [Finite K] [Finite G₁] (adv : K → TightAdv M G₁) :
    ∃ cover : Finset M, ∃ restricted : K → TightAdv {m // m ∈ cover} G₁,
      ∀ k, mapMessages Subtype.val (restricted k) = adv k := by
  obtain ⟨cover, hcover⟩ := exists_message_cover adv
  exact ⟨cover, fun k => restrictMessages cover (adv k) (hcover k),
    fun k => mapMessages_restrictMessages cover (adv k) (hcover k)⟩

end BLS.CoCDH.Tight
