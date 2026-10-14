import VCVio.OracleComp.Traversal
import VCVio.OracleComp.Support

/-! A finite, branching oracle program mentions only finitely many labels when
every answer type is finite. The cover includes queries on every syntactic path
and final outputs, so it is valid under adaptive simulation. This is a proof-only
cover: its size is not claimed polynomial and no reduction enumerates it. -/

open OracleComp OracleSpec

namespace Signatures.FiniteDomain

variable {I A M : Type} {spec : OracleSpec I}

theorem allPaths_mono {queryPred queryPred' : I → Prop} {outputPred outputPred' : A → Prop}
    {possible : (q : I) → Set (spec.Range q)} (oa : OracleComp spec A)
    (hq : ∀ q, queryPred q → queryPred' q) (ho : ∀ a, outputPred a → outputPred' a)
    (h : allPathsSatisfy queryPred outputPred possible oa) :
    allPathsSatisfy queryPred' outputPred' possible oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      simp only [allPathsSatisfy_pure] at h ⊢
      exact ho a h
  | query_bind q next ih =>
      obtain ⟨hroot, htail⟩ := (allPathsSatisfy_query_bind q next).mp h
      exact (allPathsSatisfy_query_bind q next).mpr ⟨hq q hroot, fun r hr => ih r (htail r hr)⟩

/-- One finite set covers every queried label and every output label of the
program. This does not bound the number of labels by the depth of one run. -/
theorem exists_cover [∀ q, Finite (spec.Range q)]
    (queryLabels : I → Finset M) (outputLabels : A → Finset M) (oa : OracleComp spec A) :
    ∃ cover : Finset M, allPathsSatisfy (fun q => queryLabels q ⊆ cover)
      (fun a => outputLabels a ⊆ cover) (fun _ => Set.univ) oa := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a => exact ⟨outputLabels a, by simp⟩
  | query_bind q next ih =>
      let : Fintype (spec.Range q) := Fintype.ofFinite _
      choose covers hcovers using ih
      refine ⟨queryLabels q ∪ Finset.univ.biUnion covers, ?_⟩
      apply (allPathsSatisfy_query_bind q next).mpr
      refine ⟨Finset.subset_union_left, fun r _ => ?_⟩
      have hsub : covers r ⊆ queryLabels q ∪ Finset.univ.biUnion covers := by
        intro m hm
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, hm⟩)
      exact allPaths_mono (next r) (fun _ h => h.trans hsub) (fun _ h => h.trans hsub) (hcovers r)

/-- A single cover works for a finite family of public inputs, including every
possible generated public key. It remains independent of all oracle replies. -/
theorem exists_family_cover {K : Type} [Finite K] [∀ q, Finite (spec.Range q)]
    (queryLabels : I → Finset M) (outputLabels : A → Finset M) (oa : K → OracleComp spec A) :
    ∃ cover : Finset M, ∀ k, allPathsSatisfy (fun q => queryLabels q ⊆ cover)
      (fun a => outputLabels a ⊆ cover) (fun _ => Set.univ) (oa k) := by
  classical
  let : Fintype K := Fintype.ofFinite _
  choose covers hcovers using fun k => exists_cover queryLabels outputLabels (oa k)
  refine ⟨Finset.univ.biUnion covers, fun k => ?_⟩
  have hsub : covers k ⊆ Finset.univ.biUnion covers := by
    intro m hm
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hm⟩
  exact allPaths_mono (oa k) (fun _ h => h.trans hsub) (fun _ h => h.trans hsub) (hcovers k)

end Signatures.FiniteDomain
