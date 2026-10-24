import Proofs.Runtime.ReplayFork
import VCVio.CryptoFoundations.SeededFork
import VCVio.OracleComp.SimSemantics.StateT.Basic.Native

/-! Structural bridges for fixed-private-tape replay. A fully seeded first
execution follows one ordinary query-tree path. Replacing a selected seeded
answer retains that path's prefix, including private randomness, and continues
from the selected query with the replacement answer. -/

open OracleComp OracleSpec
open PFunctor.FreeM (Path Cursor)

namespace Signatures.Runtime.SeededReplay

variable {I A : Type} {spec : OracleSpec.{0, 0} I} [DecidableEq I]

attribute [local implicit_reducible] FreeMonoid PFunctor.Idx

def run (main : OracleComp spec A) (seed : QuerySeed spec) : OracleComp spec A :=
  (simulateQ seededOracle main).run' seed

theorem run_query (i : I) (next : spec.Range i → OracleComp spec A)
    (seed : QuerySeed spec) :
    run (OracleComp.queryBind i next) seed =
      match seed i with
      | [] => (spec.query i : OracleComp spec _) >>= fun u => run (next u) seed
      | u :: us => run (next u) (seed.update i us) := by
  change ((seededOracle i >>= fun u => simulateQ seededOracle (next u)).run' seed) = _
  rw [seededOracle.run'_bind_query_eq_pop]
  cases hs : seed i <;> simp [QuerySeed.pop, hs, run]

theorem support_run_subset (main : OracleComp spec A) (seed : QuerySeed spec) :
    support (run main seed) ⊆ support main :=
  support_simulateQ_run'_subset seededOracle main seed

/-- Every answer on this path is supplied by the seed, with no live fallback. -/
def Covered (seed : QuerySeed spec) : (main : OracleComp spec A) → Path main → Prop
  | .pure _, _ => True
  | .queryBind i next, ⟨answer, tail⟩ =>
      match seed i with
      | [] => False
      | u :: us => answer = u ∧ Covered (seed.update i us) (next answer) tail

theorem covered_path_of_support (main : OracleComp spec A) (qb : I → Nat)
    (hmain : IsPerIndexQueryBound main qb) (seed : QuerySeed spec)
    (hseed : ∀ i, qb i ≤ (seed i).length) (x : A) (hx : x ∈ support (run main seed)) :
    ∃ path : Path main, PFunctor.FreeM.output main path = x ∧ Covered seed main path := by
  induction main generalizing qb seed with
  | pure a =>
      have hax : a = x := by simpa [run] using hx.symm
      subst x
      exact ⟨(), rfl, trivial⟩
  | queryBind i next ih =>
      have hb : 0 < qb i ∧ ∀ u,
          IsPerIndexQueryBound (next u) (Function.update qb i (qb i - 1)) := hmain
      cases hs : seed i with
      | nil => have := hseed i; simp [hs] at this; omega
      | cons u us =>
          rw [run_query, hs] at hx
          have hrest : ∀ j, Function.update qb i (qb i - 1) j ≤
              ((seed.update i us) j).length := by
            intro j
            by_cases hj : j = i
            · subst j
              have := hseed i
              simp [hs] at this
              simp only [Function.update_self, QuerySeed.update_self]
              omega
            · simpa [Function.update_of_ne hj, QuerySeed.update_of_ne, hj] using hseed j
          obtain ⟨path, hp, hc⟩ := ih u _ (hb.2 u) _ hrest hx
          exact ⟨⟨u, path⟩, hp, by simpa [Covered, hs] using hc⟩

/-- Keep all other families, retain the chosen family's prefix, replace its
selected answer, and leave its later answers to the live oracle. -/
def replace (seed : QuerySeed spec) (i : I) (n : Nat) (u : spec.Range i) :
    QuerySeed spec := seed.update i ((seed i).take n ++ [u])

theorem replace_eq (seed : QuerySeed spec) (i : I) (n : Nat) (u : spec.Range i) :
    replace seed i n u = (seed.takeAtIndex i n).addValue i u := by
  simp [replace, QuerySeed.takeAtIndex, QuerySeed.addValue, QuerySeed.addValues]

private theorem replace_update_other (seed : QuerySeed spec) {i j : I} (h : j ≠ i)
    (n : Nat) (u : spec.Range i) (rest : List (spec.Range j)) :
    (replace seed i n u).update j rest = replace (seed.update j rest) i n u := by
  simp only [replace, QuerySeed.update_of_ne _ _ _ _ (Ne.symm h)]
  exact QuerySeed.update_comm seed (Ne.symm h) _ _

/-- A covered first path fixes the entire prefix before its selected query.
After replacing the selected seed entry, every possible replay result comes
from that same continuation with the new answer. -/
theorem covered_occurrence {main : OracleComp spec A} {target : I} {n : Nat}
    (occ : Cursor.Occurrence target main n) (seed : QuerySeed spec)
    (old : spec.Range target) (suffix : Path (occ.resume old))
    (hc : Covered seed main (occ.plug old suffix)) :
    (seed target)[n]? = some old ∧
      ∀ fresh, support (run main (replace seed target n fresh)) ⊆
        support (occ.resume fresh) := by
  induction occ generalizing seed with
  | here next =>
      change Covered seed (OracleComp.queryBind target next) ⟨old, suffix⟩ at hc
      cases hs : seed target with
      | nil => simp [Covered, hs] at hc
      | cons u us =>
          simp only [Covered, hs] at hc
          have hh : old = u := hc.1
          subst u
          refine ⟨by simp, ?_⟩
          intro fresh
          change support (run (OracleComp.queryBind target next) _) ⊆ support (next fresh)
          simpa only [run_query, replace, QuerySeed.update_self, List.take_zero,
            List.nil_append, QuerySeed.update_idem] using
            support_run_subset (next fresh) (seed.update target [])
  | @stepSame next n prior tail ih =>
      change Covered seed (OracleComp.queryBind target next) ⟨prior, tail.plug old suffix⟩ at hc
      cases hs : seed target with
      | nil => simp [Covered, hs] at hc
      | cons u us =>
          have hh : prior = u ∧ Covered (seed.update target us) _ (tail.plug old suffix) := by
            simpa only [Covered, hs] using hc
          have heq := hh.1
          subst u
          obtain ⟨hlookup, hresume⟩ := ih (seed.update target us) suffix hh.2
          refine ⟨by simpa [hs] using hlookup, ?_⟩
          intro fresh
          change support (run (OracleComp.queryBind target next) _) ⊆ support (tail.resume fresh)
          simpa only [run_query, replace, QuerySeed.update_self, hs,
            List.take_succ_cons, List.cons_append, QuerySeed.update_idem] using hresume fresh
  | @stepOther j next n hne prior tail ih =>
      change Covered seed (OracleComp.queryBind j next) ⟨prior, tail.plug old suffix⟩ at hc
      cases hs : seed j with
      | nil => simp [Covered, hs] at hc
      | cons u us =>
          have hh : prior = u ∧ Covered (seed.update j us) _ (tail.plug old suffix) := by
            simpa only [Covered, hs] using hc
          have heq := hh.1
          subst u
          obtain ⟨hlookup, hresume⟩ := ih (seed.update j us) suffix hh.2
          refine ⟨by simpa [QuerySeed.update_of_ne, Ne.symm hne] using hlookup, ?_⟩
          intro fresh
          change support (run (OracleComp.queryBind j next) _) ⊆ support (tail.resume fresh)
          have hhead : replace seed target n fresh j = prior :: us := by
            simpa [replace, hne] using hs
          simp only [run_query, hhead]
          rw [replace_update_other seed hne]
          exact hresume fresh

omit [DecidableEq I] in
private theorem completion_mem_support {main : OracleComp spec A} {target : I} {n : Nat}
    (occ : Cursor.Occurrence target main n) (c : occ.Completion) :
    c ∈ support occ.complete := by
  change c ∈ support ((spec.query target : OracleComp spec _) >>= fun answer =>
    (fun suffix => Cursor.Occurrence.Completion.mk answer suffix) <$>
      PFunctor.FreeM.withPath (occ.resume answer))
  rw [mem_support_bind_iff]
  refine ⟨c.answer, by simp, ?_⟩
  rw [support_map]
  exact ⟨c.suffix, mem_support_replayFirstPath _ _, rfl⟩

/-- A shared occurrence with distinct answers and matching selection is an
actual successful contextual fork, not just two unrelated accepting outputs. -/
theorem context_mem_of_completion [∀ i, DecidableEq (spec.Range i)]
    (main : OracleComp spec A) (qb : I → Nat) (target : I)
    (select : A → Option (Fin (qb target + 1)))
    (path : Path main) (slot : Fin (qb target + 1))
    (located : Cursor.Located target main path slot)
    (hl : Cursor.locateAt? target main path slot = some located)
    (second : located.occurrence.Completion)
    (hs₁ : select (PFunctor.FreeM.output main path) = some slot)
    (hs₂ : select (PFunctor.FreeM.output main second.path) = some slot)
    (hne : located.completion.answer ≠ second.answer) :
    some (PFunctor.FreeM.output main path, PFunctor.FreeM.output main second.path) ∈
      support (contextFork main qb target select) := by
  rw [← Replay.loggedFork_eq_contextFork (spec := spec) main qb target select]
  unfold Replay.loggedFork
  rw [mem_support_bind_iff]
  refine ⟨replayPathResult main path,
    replayPathResult_mem_support_replayFirstRun main path (mem_support_replayFirstPath _ _), ?_⟩
  simp only [replayPathResult, pathLogResult, hs₁, Replay.splitBefore_trace, hl,
    Option.map_some]
  rw [Replay.rerun_log_completion, mem_support_bind_iff]
  refine ⟨pathLogResult main second.path, ?_, ?_⟩
  · rw [support_map]
    exact ⟨second, completion_mem_support _ _, rfl⟩
  · simp only [Cursor.Occurrence.Completion.path, Cursor.Occurrence.trace_plug,
      Cursor.Occurrence.output_plug] at hs₂ ⊢
    rw [Replay.splitBefore_before (spec := spec) located.occurrence second.answer]
    simp [hs₂, hne]

/-- Every successful fully seeded fork has the common-prefix structure of a
contextual fork. This transfers extraction invariants, not probabilities: the
two algorithms keep different private randomness after the selected query. -/
theorem seededFork_support_context [∀ i, SampleableType (spec.Range i)]
    [∀ i, DecidableEq (spec.Range i)] [unifSpec ⊂ₒ spec] [unifSpec ˡ⊂ₒ spec]
    (main : OracleComp spec A) (qb : I → Nat) (families : List I) (target : I)
    (select : A → Option (Fin (qb target + 1)))
    (hmain : IsPerIndexQueryBound main qb)
    (hcover : ∀ i, 0 < qb i → i ∈ families)
    (hreach : PathCfReachable main qb target select)
    {x₁ x₂ : A}
    (h : some (x₁, x₂) ∈ support (seededFork main qb families target select)) :
    some (x₁, x₂) ∈ support (contextFork main qb target select) := by
  unfold seededFork at h
  simp only [mem_support_bind_iff] at h
  obtain ⟨seed, hseed, first, hfirst, h⟩ := h
  cases hs₁ : select first with
  | none => simp [hs₁] at h
  | some slot =>
      simp only [hs₁] at h
      rw [mem_support_bind_iff] at h
      obtain ⟨fresh, _, h⟩ := h
      by_cases hsame : (seed target)[slot]? = some fresh
      · simp [hsame] at h
      · rw [ite_eq_right hsame, mem_support_bind_iff] at h
        obtain ⟨second, hsecond, h⟩ := h
        by_cases hs₂ : select second = some slot
        · simp only [ite_eq_left hs₂, support_pure, Set.mem_singleton_iff,
            Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hseed' : seed ∈ support (generateSeed spec qb families) := by
            simpa only [support_liftComp] using hseed
          have hlength : ∀ i, qb i ≤ (seed i).length := fun i =>
            le_length_of_mem_support_generateSeed_of_covers spec qb families seed i hseed' hcover
          obtain ⟨path, hp, hc⟩ := covered_path_of_support main qb hmain seed hlength x₁ hfirst
          have hsPath : select (PFunctor.FreeM.output main path) = some slot := by
            simpa only [hp] using hs₁
          obtain ⟨located, hl⟩ := Option.isSome_iff_exists.mp (hreach path slot hsPath)
          have hcovered : Covered seed main located.completion.path := by
            simpa only [located.path_eq] using hc
          obtain ⟨hlookup, hresume⟩ := covered_occurrence located.occurrence seed
            located.completion.answer located.completion.suffix hcovered
          have hsecond' : x₂ ∈ support (located.occurrence.resume fresh) :=
            hresume fresh (by simpa only [run, replace_eq] using hsecond)
          rw [PFunctor.FreeM.support_eq_range_output] at hsecond'
          obtain ⟨suffix, hout⟩ := hsecond'
          let completion : located.occurrence.Completion := ⟨fresh, suffix⟩
          have hout' : PFunctor.FreeM.output main completion.path = x₂ := by
            simpa [completion, Cursor.Occurrence.Completion.path] using hout
          have hne : located.completion.answer ≠ completion.answer := by
            intro heq
            exact hsame (by simpa only [Fin.getElem?_fin, completion, heq] using hlookup)
          simpa only [hp, hout'] using context_mem_of_completion main qb target select
            path slot located hl completion hsPath (by simpa only [hout'] using hs₂) hne
        · simp [hs₂] at h

/-- Extra seed capacity does not add a candidate fork position. Summing only
the selector's actual labels keeps the denominator equal to their number. -/
theorem seededFork_success_bound_labels [∀ i, SampleableType (spec.Range i)]
    [∀ i, DecidableEq (spec.Range i)] [unifSpec ⊂ₒ spec] [unifSpec ˡ⊂ₒ spec]
    [IsUniformSpec spec]
    (main : OracleComp spec A) (qb : I → Nat) (families : List I) (target : I)
    {q : Nat} (select : A → Option (Fin q))
    (embed : Fin q → Fin (qb target + 1)) (hinj : Function.Injective embed) :
    let acc : ENNReal := ∑ s, Pr[= some s | select <$> main]
    acc * (acc / q - (Fintype.card (spec.Range target) : ENNReal)⁻¹) ≤
      Pr[fun r => r.isSome |
        seededFork main qb families target (Option.map embed ∘ select)] := by
  classical
  let ps : Fin q → ENNReal := fun s => Pr[= some s | select <$> main]
  have hsum : (∑ s, ps s) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (sum_probOutput_some_le_one (mx := select <$> main))
  have hquad := ENNReal.mul_tsub_inv_le_sum_sq_sub_div
    (Finset.univ : Finset (Fin q)) ps
    (Fintype.card (spec.Range target) : ENNReal) hsum
  simp only [Finset.card_univ, Fintype.card_fin] at hquad
  refine hquad.trans ((Finset.sum_le_sum fun s _ => ?_).trans
    (sum_probEvent_option_map_eq_some_le_isSome (mx :=
      seededFork main qb families target (Option.map embed ∘ select))
      (select ∘ Prod.fst)))
  have hslot := le_probOutput_seededFork main qb families target
    (Option.map embed ∘ select) (embed s)
  have hprob : Pr[= some (embed s) | (Option.map embed ∘ select) <$> main] = ps s := by
    simpa only [Functor.map_map, Function.comp_def, ps] using
      probOutput_some_map_option_map (select <$> main) hinj s
  rw [hprob] at hslot
  refine hslot.trans_eq (probEvent_ext fun r _ => ?_)
  cases r with
  | none => simp
  | some pair => simp [Function.comp_def, Option.map_eq_some_iff, hinj.eq_iff]

/-- Increasing the seed budget while embedding the same numerical fork
positions leaves the common-prefix extraction invariant unchanged. -/
theorem contextFork_support_castLE [∀ i, DecidableEq (spec.Range i)]
    (main : OracleComp spec A) (small large : I → Nat) (target : I)
    (hle : small target ≤ large target)
    (select : A → Option (Fin (small target + 1))) {x₁ x₂ : A}
    (h : some (x₁, x₂) ∈ support (contextFork main large target
      (Option.map (Fin.castLE (Nat.succ_le_succ hle)) ∘ select))) :
    some (x₁, x₂) ∈ support (contextFork main small target select) := by
  obtain ⟨path, s, located, second, _, hs₁, _, hne, hs₂, rfl, rfl⟩ :=
    contextFork_success main large target _ h
  simp only [Function.comp_def, Option.map_eq_some_iff] at hs₁ hs₂
  obtain ⟨slot, hs₁, rfl⟩ := hs₁
  obtain ⟨slot₂, hs₂, heq⟩ := hs₂
  have heq' : slot₂ = slot :=
    Fin.ext (congrArg (fun x : Fin (large target + 1) => x.val) heq)
  subst slot₂
  have hl : Cursor.locateAt? target main path slot = some located := by
    rcases located with ⟨occ, first, rfl⟩
    exact Cursor.locateAt?_completion_path occ first
  exact context_mem_of_completion main small target select path slot located hl second hs₁ hs₂ hne

end Signatures.Runtime.SeededReplay
