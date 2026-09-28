/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.BLS.CoCDH.Spec.Coron
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Lazy Coron coins

The Coron reduction needs one persistent uniform coin per message.  This module realizes those
coins with VCVio's lazy random oracle while forwarding the reduction's ordinary uniform samples.
The main theorem couples that implementation to a full coin table.  The table appears only in the
proof: the executable reduction samples and caches a coin exactly when its message is queried.
-/

open OracleComp OracleSpec

namespace BLS.CoCDH

variable {D R : Type} [DecidableEq D] [Finite D] [Finite R] [Nonempty R]
  [SampleableType R] [SampleableType (D → R)]

/-- Interpret ordinary uniform queries honestly and coin queries from the fixed table `g`. -/
noncomputable def coinTableImpl (g : D → R) :
    QueryImpl (unifSpec + (D →ₒ R)) ProbComp :=
  (QueryImpl.ofLift unifSpec ProbComp) +
    (QueryImpl.ofFn g).liftTarget ProbComp

private lemma evalSPMF_uniformSample_bind_update_bind {α : Type} (t : D)
    (ψ : (D → R) → ProbComp α) :
    𝒮[do let u ← $ᵗ R; let g ← $ᵗ (D → R); ψ (Function.update g t u)] =
      𝒮[do let g ← $ᵗ (D → R); ψ g] := by
  have h : 𝒮[(do
      let u ← $ᵗ R
      let g ← $ᵗ (D → R)
      pure (Function.update g t u)) >>= ψ] = 𝒮[($ᵗ (D → R)) >>= ψ] := by
    rw [evalSPMF_bind, evalSPMF_uniformSample_bind_update, evalSPMF_bind]
  simpa only [bind_assoc, pure_bind] using h

/-- Running a computation with lazy cached coins has the same output distribution as first sampling
a full independent coin table and interpreting every coin query from that table.  Uniform-sampling
queries in the computation remain probabilistic and are merely forwarded on both sides. -/
theorem evalSPMF_lazyCoin_eq_table {α : Type}
    (oa : OracleComp (unifSpec + (D →ₒ R)) α)
    (c : (D →ₒ R).QueryCache) :
    𝒮[(simulateQ (lazyCoinImpl (D := D) (R := R)) oa).run' c] =
      𝒮[do let g ← $ᵗ (D → R);
            simulateQ (coinTableImpl (tableExtending c g)) oa] := by
  classical
  letI := Fintype.ofFinite D
  letI := Fintype.ofFinite R
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
      simp only [simulateQ_pure]
      change 𝒮[(pure a : ProbComp α)] =
        𝒮[do let _g ← $ᵗ (D → R); pure a]
      symm
      exact DeferredSampling.evalSPMF_bind_const_neverFails _ (by simp) _
  | query_bind t k ih =>
      cases t with
      | inl T =>
          have hL :
              (simulateQ (lazyCoinImpl (D := D) (R := R))
                  (liftM ((unifSpec + (D →ₒ R)).query (Sum.inl T)) >>= k)).run' c =
                ((unifSpec.query T : ProbComp (unifSpec.Range T)) >>= fun u =>
                  (simulateQ (lazyCoinImpl (D := D) (R := R)) (k u)).run' c) := by
            simp [lazyCoinImpl, unifFwdImpl]
          have hR :
              (do let g ← $ᵗ (D → R)
                  simulateQ (coinTableImpl (tableExtending c g))
                    (liftM ((unifSpec + (D →ₒ R)).query (Sum.inl T)) >>= k)) =
                (do let g ← $ᵗ (D → R)
                    let u ← (unifSpec.query T : ProbComp (unifSpec.Range T))
                    simulateQ (coinTableImpl (tableExtending c g)) (k u)) := by
            simp [coinTableImpl]
          rw [hL, hR]
          calc
            𝒮[(unifSpec.query T : ProbComp (unifSpec.Range T)) >>= fun u =>
                (simulateQ (lazyCoinImpl (D := D) (R := R)) (k u)).run' c] =
                𝒮[(unifSpec.query T : ProbComp (unifSpec.Range T)) >>= fun u =>
                  ($ᵗ (D → R)) >>= fun g =>
                    simulateQ (coinTableImpl (tableExtending c g)) (k u)] := by
              exact evalSPMF_bind_congr' _ (fun u => ih u c)
            _ = 𝒮[($ᵗ (D → R)) >>= fun g =>
                  (unifSpec.query T : ProbComp (unifSpec.Range T)) >>= fun u =>
                    simulateQ (coinTableImpl (tableExtending c g)) (k u)] := by
              exact DeferredSampling.evalSPMF_bind_comm _ _ _
      | inr d =>
          have hL :
              (simulateQ (lazyCoinImpl (D := D) (R := R))
                  (liftM ((unifSpec + (D →ₒ R)).query (Sum.inr d)) >>= k)).run' c =
                ((randomOracle (spec := (D →ₒ R)) d).run c) >>= fun p =>
                  (simulateQ (lazyCoinImpl (D := D) (R := R)) (k p.1)).run' p.2 := by
            rw [simulateQ_bind, simulateQ_spec_query]
            change Prod.fst <$> (((randomOracle (spec := (D →ₒ R)) d).run c) >>= fun p =>
              (simulateQ (lazyCoinImpl (D := D) (R := R)) (k p.1)).run p.2) = _
            rw [map_bind]
            rfl
          have hR :
              (do let g ← $ᵗ (D → R)
                  simulateQ (coinTableImpl (tableExtending c g))
                    (liftM ((unifSpec + (D →ₒ R)).query (Sum.inr d)) >>= k)) =
                (do let g ← $ᵗ (D → R)
                    simulateQ (coinTableImpl (tableExtending c g))
                      (k (tableExtending c g d))) := by
            refine bind_congr fun g => ?_
            rw [simulateQ_bind, simulateQ_spec_query]
            change (pure (tableExtending c g d) >>= fun x =>
              simulateQ (coinTableImpl (tableExtending c g)) (k x)) = _
            rw [pure_bind]
          rw [hL, hR]
          cases hc : c d with
          | none =>
              rw [show ((randomOracle (spec := (D →ₒ R)) d).run c) =
                    (fun u => (u, c.cacheQuery d u)) <$> ($ᵗ R) from
                    QueryImpl.withCaching_run_none _ hc]
              rw [show (((fun u => (u, c.cacheQuery d u)) <$> ($ᵗ R)) >>=
                    fun p : R × (D →ₒ R).QueryCache =>
                      (simulateQ (lazyCoinImpl (D := D) (R := R)) (k p.1)).run' p.2) =
                    (($ᵗ R) >>= fun u =>
                      (simulateQ (lazyCoinImpl (D := D) (R := R)) (k u)).run'
                        (c.cacheQuery d u)) by
                  rw [map_eq_bind_pure_comp]
                  simp [bind_assoc]]
              let ψ : (D → R) → ProbComp α := fun g' =>
                simulateQ (coinTableImpl (tableExtending c g'))
                  (k (tableExtending c g' d))
              have hfun : ∀ u : R,
                  (fun g : D → R =>
                    simulateQ (coinTableImpl (tableExtending (c.cacheQuery d u) g)) (k u)) =
                  fun g : D → R => ψ (Function.update g d u) := by
                intro u
                funext g
                simp only [ψ]
                rw [tableExtending_cacheQuery, ← tableExtending_update_of_none c g hc u]
                congr 2
                simp [tableExtending, hc]
              calc
                𝒮[($ᵗ R) >>= fun u =>
                    (simulateQ (lazyCoinImpl (D := D) (R := R)) (k u)).run'
                      (c.cacheQuery d u)] =
                    𝒮[($ᵗ R) >>= fun u => ($ᵗ (D → R)) >>= fun g =>
                      simulateQ (coinTableImpl (tableExtending (c.cacheQuery d u) g)) (k u)] := by
                  exact evalSPMF_bind_congr' _ (fun u => ih u (c.cacheQuery d u))
                _ = 𝒮[($ᵗ R) >>= fun u => ($ᵗ (D → R)) >>= fun g =>
                      ψ (Function.update g d u)] := by
                  refine evalSPMF_bind_congr' _ fun u => ?_
                  rw [hfun u]
                _ = 𝒮[($ᵗ (D → R)) >>= fun g => ψ g] :=
                  evalSPMF_uniformSample_bind_update_bind d ψ
          | some u =>
              rw [show ((randomOracle (spec := (D →ₒ R)) d).run c) =
                    (pure (u, c) : ProbComp _) from QueryImpl.withCaching_run_some _ hc,
                  pure_bind]
              rw [ih u c]
              refine congrArg evalSPMF ?_
              refine bind_congr fun g => ?_
              have hcell : tableExtending c g d = u := by simp [tableExtending, hc]
              congr 2
              exact hcell.symm

end BLS.CoCDH
