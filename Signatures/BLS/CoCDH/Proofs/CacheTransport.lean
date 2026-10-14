import Signatures.BLS.CoCDH.Spec.Coron
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-! Injective label transport for a shared lazy cache with private randomness.
These exact laws apply to any adaptive client and any message domain. -/

open OracleComp OracleSpec

namespace BLS.CoCDH.MessageTransport

variable {N M R : Type} (f : N → M)

def projectCache (c : (M →ₒ R).QueryCache) : (N →ₒ R).QueryCache :=
  QueryCache.ofFn (fun n => c (f n))

@[simp] theorem projectCache_apply (c : (M →ₒ R).QueryCache) (n : N) :
    projectCache f c n = c (f n) := rfl

@[simp] theorem projectCache_empty : projectCache (R := R) f ∅ = ∅ := rfl

def baseQueries : QueryImpl (unifSpec + (N →ₒ R)) (OracleComp (unifSpec + (M →ₒ R))) :=
  fun q => match q with
    | .inl n => query (spec := unifSpec + (M →ₒ R)) (.inl n)
    | .inr n => query (spec := unifSpec + (M →ₒ R)) (.inr (f n))

theorem baseQueries_lift {α : Type} (oa : ProbComp α) :
    simulateQ (baseQueries f) (liftM oa : OracleComp (unifSpec + (N →ₒ R)) α) =
      (liftM oa : OracleComp (unifSpec + (M →ₒ R)) α) := by
  have h := QueryImpl.simulateQ_liftM_eq_of_query (baseQueries (R := R) f)
    (QueryImpl.ofLift unifSpec (OracleComp (unifSpec + (M →ₒ R))))
    (fun n => by
      rw [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_liftM_query]
      simp [OracleComp.liftM_eq_liftM_liftM, baseQueries]) oa
  exact h.trans (OracleComp.liftComp_eq_liftM oa)

variable [DecidableEq N] [DecidableEq M] (hf : Function.Injective f)

include hf

theorem projectCache_update (c : (M →ₒ R).QueryCache) (n : N) (r : R) :
    projectCache f (c.cacheQuery (f n) r) = (projectCache f c).cacheQuery n r := by
  apply QueryCache.ext
  intro k
  by_cases h : k = n
  · subst k
    simp
  · have hfn : f k ≠ f n := fun he => h (hf he)
    simp [h, hfn]

theorem randomOracle_project [SampleableType R] (c : (M →ₒ R).QueryCache) (n : N) :
    Prod.map id (projectCache f) <$> ((M →ₒ R).randomOracle (f n)).run c =
      ((N →ₒ R).randomOracle n).run (projectCache f c) := by
  rw [randomOracle.run_eq, randomOracle.run_eq]
  cases h : c (f n) <;> simp [h, projectCache_update f hf]

variable [SampleableType R]

theorem lazyQuery_project (q : (unifSpec + (N →ₒ R)).Domain) (c : (M →ₒ R).QueryCache) :
    Prod.map id (projectCache f) <$>
      (simulateQ CoCDH.lazyCoinImpl (baseQueries f q)).run c =
      (CoCDH.lazyCoinImpl q).run (projectCache f c) := by
  rcases q with n | m
  · simp [baseQueries, CoCDH.lazyCoinImpl, unifFwdImpl, Functor.map_map]
  · simp only [baseQueries, simulateQ_HasQuery_query]
    exact randomOracle_project f hf c m

theorem lazyRun_project {α : Type} (oa : OracleComp (unifSpec + (N →ₒ R)) α)
    (c : (M →ₒ R).QueryCache) :
    Prod.map id (projectCache f) <$>
      (simulateQ CoCDH.lazyCoinImpl (simulateQ (baseQueries f) oa)).run c =
      (simulateQ CoCDH.lazyCoinImpl oa).run (projectCache f c) := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind q next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← lazyQuery_project f hf q c, bind_map_left]
    exact bind_congr fun p => ih p.1 p.2

theorem lazyRun_rename {α : Type} (oa : OracleComp (unifSpec + (N →ₒ R)) α) :
    (simulateQ CoCDH.lazyCoinImpl (simulateQ (baseQueries f) oa)).run' ∅ =
      (simulateQ CoCDH.lazyCoinImpl oa).run' ∅ := by
  have h := congrArg (fun comp => Prod.fst <$> comp) (lazyRun_project f hf oa ∅)
  simpa only [StateT.run'_eq, Functor.map_map, Function.comp_def, Prod.map_fst,
    id_eq, projectCache_empty] using h

end BLS.CoCDH.MessageTransport
