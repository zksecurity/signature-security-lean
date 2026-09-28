import Signatures.Runtime.CoronReduction
import Signatures.Runtime.CoronRefinement
import Signatures.Runtime.CoronErasure
import Signatures.Runtime.CoronMachine
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open Signatures.Runtime OracleComp OracleSpec

namespace SignaturesTest.RuntimeCoron

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5
private def cost := PrimitiveCosts.unit
private def sampling : Coron.SamplingCosts := ⟨1, 1, 1⟩
private def machineSampling : Machine.SamplingCosts := ⟨1, fun _ => 1⟩
private def primitives := arithmetic F F F Bool Bool cost

-- Even a source that makes no queries must pay for the verification hash and extraction.
private def noQueries : Program CryptoOp (Coron.Command 1) [message, point₁] (.pair message point₁) :=
  .ret (.pair (.var .here) (.var (.there .here)))

private theorem noQueries_budget (m : Bool) (sigma : F) :
    SourceBudget primitives (Coron.replies 1) Coron.kind noQueries (m, sigma, ()) 5 (fun _ => 0) := by
  intro price z hz
  simp only [noQueries, Program.run, support_pure, Set.mem_singleton_iff] at hz
  subst z
  simp [Expr.run, Var.depth]

example (m : Bool) (sigma : F) :
    Run.value <$> Coron.reduction (F := F) (G₂ := F) cost sampling 1 2 3 0 1 noQueries (m, sigma, ()) =
      BLS.CoCDH.coronReductionLazyPK (F := F) 0
        (BLS.CoCDH.Tight.cacheForgeryPK
          (fun _ : F => (pure (m, sigma) : OracleComp (BLS.CoCDH.Tight.advSpec Bool F) (Bool × F)))) 1 1 2 4 3 :=
  Coron.reduction_erase cost sampling 1 2 3 1 4 0 1 noQueries (m, sigma, ())
    (fun _ : F => (pure (m, sigma) : OracleComp (BLS.CoCDH.Tight.advSpec Bool F) (Bool × F))) rfl

example (m : Bool) (sigma : F) (z : Run F)
    (hz : z ∈ support (Coron.reduction (F := F) (G₂ := F) cost sampling (1 : F) 2 3 0 1 noQueries (m, sigma, ()))) :
    z.steps ≤ 203 := by
  have hb := Coron.reduction_bound (F := F) (G₂ := F) cost sampling (1 : F) 2 3 0 1 noQueries
    (m, sigma, ()) 5 (fun _ => 0) (noQueries_budget m sigma) z hz
  simpa [Coron.reductionBound, Coron.finishBound, Coron.replyBase, cost, sampling,
    PrimitiveCosts.unit] using hb

example (m : Bool) (sigma : F) (z : Run F)
    (hz : z ∈ support (Coron.reduction (F := F) (G₂ := F) cost sampling (1 : F) 2 3 0 1 noQueries (m, sigma, ()))) :
    16 ≤ z.steps := by
  simp only [Coron.reduction, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨p, _, r, _, rfl⟩ := hz
  exact Nat.le_add_left _ _

private def cached : Coron.CacheState F Bool 1 := ⟨[(false, 2)], [(false, 0)], [false]⟩

-- Cached scalar/coin replies do not execute the sampler; the list scans are still charged.
private theorem cached_hash : (Coron.reply (F := F) (G₂ := F) cost sampling (1 : F) 2 3 1 false false).run cached =
    pure (⟨0, 145⟩, cached) := by
  norm_num [Coron.reply, Coron.coinValue, Coron.hashReply, Coron.signReply, cached,
    cacheHandler, cacheGet, lookup, lookupBody, Program.run, Expr.run, Var.get, Var.depth,
    foldRun, StateT.run, cost, arithmetic, CryptoOp.price, PrimitiveCosts.unit, smul_eq_mul]
  decide

-- Repeated signing is represented as a list insertion, whose set abstraction stays unchanged.
private theorem cached_sign : (Coron.reply (F := F) (G₂ := F) cost sampling (1 : F) 2 3 1 true false).run cached =
    pure (⟨0, 135⟩, ⟨[(false, 2)], [(false, 0)], [false, false]⟩) := by
  norm_num [Coron.reply, Coron.coinValue, Coron.hashReply, Coron.signReply, cached,
    cacheHandler, cacheGet, lookup, lookupBody, Program.run, Expr.run, Var.get, Var.depth,
    foldRun, StateT.run, cost, arithmetic, CryptoOp.price, PrimitiveCosts.unit]

-- These counts come from the closed machine, including all store and call-frame work.
example : ((Coron.machineReply 1 false).run primitives
    (Machine.effects machineSampling (Coron.machineStore 1)) (false, ())).run
      (Coron.machineState (1 : F) 2 3 cached) =
    pure (⟨0, 193⟩, Coron.machineState (1 : F) 2 3 cached) := by
  unfold primitives
  rw [Coron.machineReply_run (G₂ := F) cost machineSampling (1 : F) 2 3 1 false false cached]
  have hr : (Coron.reply (F := F) (G₂ := F) cost (Coron.machineSampling machineSampling 1)
      (1 : F) 2 3 1 false false).run cached = pure (⟨0, 145⟩, cached) := cached_hash
  rw [hr]
  simp [cost, PrimitiveCosts.unit]

example : ((Coron.machineReply 1 true).run primitives
    (Machine.effects machineSampling (Coron.machineStore 1)) (false, ())).run
      (Coron.machineState (1 : F) 2 3 cached) =
    pure (⟨0, 181⟩, Coron.machineState (1 : F) 2 3
      ⟨[(false, 2)], [(false, 0)], [false, false]⟩) := by
  unfold primitives
  rw [Coron.machineReply_run (G₂ := F) cost machineSampling (1 : F) 2 3 1 true false cached]
  have hr : (Coron.reply (F := F) (G₂ := F) cost (Coron.machineSampling machineSampling 1)
      (1 : F) 2 3 1 true false).run cached =
      pure (⟨0, 135⟩, ⟨[(false, 2)], [(false, 0)], [false, false]⟩) := cached_sign
  rw [hr]
  simp [cost, PrimitiveCosts.unit]

private def adaptive : Program CryptoOp (Coron.Command 1) [message] point₁ :=
  .bind (.query (.random 1) .unit)
    (.branch (.op .natEq (.pair (.op (.finVal 1) (.var .here)) (.nat 0)))
      (.query .hash (.var (.there .here))) (.query .sign (.var (.there .here))))

private theorem adaptive_budget (m : Bool) :
    SourceBudget primitives (Coron.replies 1) Coron.kind adaptive (m, ()) 14 (fun _ => 1) := by
  intro price z hz
  simp only [adaptive, Program.run, Expr.run, Var.get, Var.depth, primitives, arithmetic,
    CryptoOp.price, cost, PrimitiveCosts.unit, pricedRequests, pure_bind, bind_assoc,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, _, z, hz, rfl⟩ := hz
  split at hz <;>
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz <;>
    obtain ⟨s, _, rfl⟩ := hz <;>
    simp [Coron.kind, Fin.sum_univ_succ] <;> omega

-- Which oracle is called depends on the previous random reply, not on a fixed query list.
example (m : Bool) :
    StateRefines Coron.CacheState.repr
      (Run.value <$> adaptive.run primitives (Coron.handler cost sampling (1 : F) 2 3 1 1) (m, ()))
      (simulateQ (Coron.nativeOracle (F := F) 1 2 3 1)
        (adaptive.denote primitives (Coron.sourceSemantics 1) (m, ()))) :=
  Coron.simulation_refines cost sampling 1 2 3 1 1 adaptive (m, ())

example (m : Bool) :
    StateRefines (Coron.machineState (1 : F) 2 3)
      (Run.value <$> adaptive.run primitives
        (Coron.handler cost (Coron.machineSampling machineSampling 1) (1 : F) 2 3 1 1) (m, ()))
      (Run.value <$> (adaptive.inline (Coron.machineRoutines 1 1)).run primitives
        (Machine.effects machineSampling (Coron.machineStore 1)) (m, ())) :=
  Coron.machineSimulation_refines cost machineSampling 1 2 3 1 1 adaptive (m, ())

example (m : Bool) (z : Run F × (Coron.machineStore 1).Value (cryptoBase F F F Bool Bool))
    (hz : z ∈ support (((adaptive.inline (Coron.machineRoutines 1 1)).run primitives
      (Machine.effects machineSampling (Coron.machineStore 1)) (m, ())).run
        (Coron.machineState (1 : F) 2 3 .empty))) :
    z.1.steps ≤ 725 := by
  have hb := Coron.machineSimulation_bound cost machineSampling (1 : F) 2 3 1 1 adaptive
    (m, ()) 14 (fun _ => 1) (adaptive_budget m) z hz
  have hsup : (Finset.univ.sup fun _ : Fin 2 => (1 : Nat)) = 1 := by decide
  simpa [Coron.machinePrices, Coron.machineSampling, Coron.replyBase, machineSampling,
    cost, PrimitiveCosts.unit, Fin.sum_univ_succ, hsup] using hb.2

end SignaturesTest.RuntimeCoron

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Program.run_refines, ``Program.denote_refines, ``Program.denote_simulate,
      ``Program.countCalls_refines, ``SourceBudget.linear_state_bound,
      ``cacheHandler_getDlogS, ``cacheHandler_randomOracle,
      ``Coron.reply_bound, ``Coron.simulation_bound, ``Coron.finish_bound, ``Coron.reduction_bound,
      ``Coron.reply_refines, ``Coron.handler_refines, ``Coron.simulation_refines,
      ``Coron.nativeOracle_original, ``Coron.nativeOracle_run,
      ``Coron.finish_erase, ``Coron.reduction_erase_native,
      ``Coron.nativeReduction_original, ``Coron.reduction_erase,
      ``cacheGet_run_state, ``Coron.machineScalarCache_run, ``Coron.machineCoinCache_run,
      ``Coron.machineReply_run, ``Coron.machineReply_bound, ``Coron.machineHandler_run,
      ``Coron.machineHandler_bound, ``Coron.machineSimulation_bound,
      ``Coron.machineHandler_erase, ``Coron.machineHandler_refines,
      ``Coron.machineSimulation_refines] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
