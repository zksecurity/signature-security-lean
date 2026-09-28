import Signatures.Runtime.AGMSimulation
import Signatures.Runtime.KeyEquality
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open Signatures.Runtime Signatures.Runtime.AGM OracleComp OracleSpec

namespace SignaturesTest.RuntimeAGMSimulation

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5
private def cost := PrimitiveCosts.unit
private def sampling : Machine.SamplingCosts := ⟨1, fun _ => 1⟩
private def primitives := arithmetic F F F Bool Unit cost
private def hash := goodHash KeyEquality.bls
private def sign := goodSign Weights.bls
private abbrev goodStore := oracleStore key key (goodConfig key)
private abbrev badStore := oracleStore key key (badConfig key)

example : (groupWeightedSum Weights.bls).run primitives
    (false, [(false, 2), (true, 3)], ()) = ⟨2, 85⟩ := rfl

example : hash.run primitives (false, ((1 : F), 2, [(false, 2), (true, 3)]), ()) = ⟨2, 72⟩ := rfl
example : sign.run primitives (false, ((1 : F), 2, [(false, 2), (true, 3)]), ()) = ⟨4, 105⟩ := rfl
example : (badHash KeyEquality.bls).run primitives
    (false, ((2 : F), [(false, 2), (true, 3)]), ()) = ⟨2, 61⟩ := rfl
example : (badSign Weights.bls).run primitives
    (false, ((2 : F), [(false, 2), (true, 3)]), ()) = ⟨4, 103⟩ := rfl

private def adaptive : Program CryptoOp (Command key key 1) [key, key] point₁ :=
  .bind (.query .hash (.var .here))
    (.branch (.op .point₁Eq (.pair (.var .here) (.op .zero₁ .unit)))
      (.query .sign (.var (.there (.there .here))))
      (.query .hash (.var (.there (.there .here)))))

private def budgets (k : Fin 3) : Nat := if k = 0 then 0 else if k = 1 then 2 else 1

private theorem adaptive_budget (i m : Bool) :
    SourceBudget primitives (replies 1) kind adaptive (i, m, ()) 15 budgets := by
  intro price z hz
  simp only [adaptive, Program.run, Expr.run, Var.get, Var.depth, primitives, arithmetic,
    CryptoOp.price, cost, PrimitiveCosts.unit, pricedRequests, pure_bind, bind_assoc,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, _, z, hz, rfl⟩ := hz
  split at hz <;>
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz <;>
    obtain ⟨s, _, rfl⟩ := hz <;>
    simp [kind, budgets, Fin.sum_univ_succ] <;> omega

private def cfgZero : (goodConfig key).Value (cryptoBase F F F Bool Unit) :=
  (1, 2, [(false, 0), (true, 3)])

private def cfgNonzero : (goodConfig key).Value (cryptoBase F F F Bool Unit) :=
  (1, 2, [(false, 1), (true, 3)])

-- The previous hash answer determines the next oracle call. Internal tables stay unchanged.
example : (((adaptive.inline (machineRoutines hash sign 1)).run primitives
    (Machine.effects sampling goodStore) (false, true, ())).run (cfgZero, [], [])) =
    pure (⟨1, 278⟩, (cfgZero, [(false, 0)], [(true, 1)])) := by
  rw [Program.inline_run]
  change (adaptive.run primitives (machineHandler cost sampling hash sign 1) (false, true, ())).run
    (cfgZero, [], []) = _
  have hh : (machineHandler (F := F) (G₁ := F) (G₂ := F) (K := Bool) (M := Unit)
      cost sampling hash sign 1 .hash false).run (cfgZero, [], []) =
      pure (⟨(0 : F), 115⟩, (cfgZero, [(false, 0)], [])) := by
    rw [machineHandler_hash_run]
    rfl
  have hs : (machineHandler (F := F) (G₁ := F) (G₂ := F) (K := Bool) (M := Unit)
      cost sampling hash sign 1 .sign true).run
      (cfgZero, [(false, (0 : F))], []) =
      pure (⟨(1 : F), 148⟩, (cfgZero, [(false, 0)], [(true, 1)])) := by
    rw [machineHandler_sign_run]
    rfl
  simp only [adaptive, Program.run, Expr.run, Var.get, Var.depth,
    StateT.run_bind, StateT.run_pure, hh, pure_bind]
  norm_num [primitives, arithmetic, CryptoOp.price, cost, PrimitiveCosts.unit]
  dsimp [cost, PrimitiveCosts.unit] at hs
  rw [hs]
  norm_num

-- Both explicit hash replies remain in the transcript; reversed storage is intentional.
example : (((adaptive.inline (machineRoutines hash sign 1)).run primitives
    (Machine.effects sampling goodStore) (false, true, ())).run (cfgNonzero, [], [])) =
    pure (⟨3, 262⟩, (cfgNonzero, [(true, 3), (false, 1)], [])) := by
  rw [Program.inline_run]
  change (adaptive.run primitives (machineHandler cost sampling hash sign 1) (false, true, ())).run
    (cfgNonzero, [], []) = _
  have hfirst : (machineHandler (F := F) (G₁ := F) (G₂ := F) (K := Bool) (M := Unit)
      cost sampling hash sign 1 .hash false).run (cfgNonzero, [], []) =
      pure (⟨(1 : F), 115⟩, (cfgNonzero, [(false, 1)], [])) := by
    rw [machineHandler_hash_run]
    rfl
  have hsecond : (machineHandler (F := F) (G₁ := F) (G₂ := F) (K := Bool) (M := Unit)
      cost sampling hash sign 1 .hash true).run
      (cfgNonzero, [(false, (1 : F))], []) =
      pure (⟨(3 : F), 132⟩, (cfgNonzero, [(true, 3), (false, 1)], [])) := by
    rw [machineHandler_hash_run]
    rfl
  simp only [adaptive, Program.run, Expr.run, Var.get, Var.depth,
    StateT.run_bind, StateT.run_pure, hfirst, pure_bind]
  norm_num [primitives, arithmetic, CryptoOp.price, cost, PrimitiveCosts.unit]
  dsimp [cost, PrimitiveCosts.unit] at hsecond
  rw [hsecond]
  norm_num

example : transcriptView (id : Bool → Bool) (id : Bool → Bool)
    ([(true, (3 : F)), (false, 1)], [(false, 2), (true, 4)]) =
    ([(false, 1), (true, 3)], [(true, 4), (false, 2)]) := rfl

-- Private randomness is forwarded unchanged, charged, and absent from both reply logs.
example (cfg : (goodConfig key).Value (cryptoBase F F F Bool Unit))
    (tr : (transcriptTy key key).Value (cryptoBase F F F Bool Unit)) :
    (machineHandler cost sampling hash sign 1 (.random 1) ()).run (cfg, tr) =
      (fun x => (⟨x, 6⟩, (cfg, tr))) <$> (liftM (unifSpec.query 1) : ProbComp (Fin 2)) := by
  exact machineHandler_random_run cost sampling hash sign 1 1 (cfg, tr)

example (cfg : (goodConfig key).Value (cryptoBase F F F Bool Unit))
    (tr : (transcriptTy key key).Value (cryptoBase F F F Bool Unit)) (i m : Bool) :
    (fun z => (z.1.value, transcriptView id id z.2.2)) <$>
      (((adaptive.inline (machineRoutines hash sign 1)).run primitives
        (Machine.effects sampling goodStore) (i, m, ())).run (cfg, tr)) =
      (simulateQ (Model.LazyAGM.fixedImpl
        (fun j => hash.denote primitives (j, cfg, ()))
        (fun n => sign.denote primitives (n, cfg, ())))
        (adaptive.denote primitives (sourceSemantics id id 1) (i, m, ()))).run
        (transcriptView id id tr) := by
  exact machineSimulation_erase cost sampling hash sign id id
    (fun cfg j => hash.denote primitives (j, cfg, ()))
    (fun cfg n => sign.denote primitives (n, cfg, ()))
    (fun _ _ => rfl) (fun _ _ => rfl) 1 adaptive (i, m, ()) cfg tr

example (i m : Bool) (z : Run F × goodStore.Value (cryptoBase F F F Bool Unit))
    (hz : z ∈ support (((adaptive.inline (machineRoutines hash sign 1)).run primitives
      (Machine.effects sampling goodStore) (i, m, ())).run (cfgNonzero, [], []))) :
    z.2.1 = cfgNonzero ∧ transcriptSize z.2 ≤ 3 ∧ z.1.steps ≤ 431 := by
  have h := goodSimulation_bound cost sampling KeyEquality.bls Weights.bls 1 6 10
    (fun x y => le_of_eq (KeyEquality.bls_steps cost x y))
    (fun i m => le_of_eq (Weights.bls_steps cost i m))
    1 2 [(false, 1), (true, 3)] adaptive (i, m, ()) 15 budgets (adaptive_budget i m) z hz
  simpa [goodHashBound, goodSignBound, machinePrices, budgets, sampling, cost,
    PrimitiveCosts.unit, Fin.sum_univ_succ, cfgNonzero] using h

example (i m : Bool) (z : Run F × badStore.Value (cryptoBase F F F Bool Unit))
    (hz : z ∈ support (((adaptive.inline
      (machineRoutines (badHash KeyEquality.bls) (badSign Weights.bls) 1)).run primitives
      (Machine.effects sampling badStore) (i, m, ())).run
      (((2 : F), [(false, 2), (true, 3)]), [], []))) :
    z.2.1 = ((2 : F), [(false, 2), (true, 3)]) ∧ transcriptSize z.2 ≤ 3 ∧ z.1.steps ≤ 407 := by
  have h := badSimulation_bound cost sampling KeyEquality.bls Weights.bls 1 6 10
    (fun x y => le_of_eq (KeyEquality.bls_steps cost x y))
    (fun i m => le_of_eq (Weights.bls_steps cost i m))
    2 [(false, 2), (true, 3)] adaptive (i, m, ()) 15 budgets (adaptive_budget i m) z hz
  simpa [badHashBound, badSignBound, machinePrices, budgets, sampling, cost,
    PrimitiveCosts.unit, Fin.sum_univ_succ] using h

end SignaturesTest.RuntimeAGMSimulation

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``groupWeightedBody_run, ``groupWeightedSum_value, ``groupWeightedSum_steps_le,
      ``groupWeightedSum_native, ``machineHash_run, ``machineSign_run, ``machineHandler_run,
      ``machineHandler_hash_run, ``machineHandler_sign_run, ``machineHandler_random_run,
      ``machineHandler_bound, ``machineSimulation_bound, ``handler_refines, ``reference_embed,
      ``machineSimulation_erase, ``goodHash_run, ``goodSign_run, ``badHash_run, ``badSign_run,
      ``goodHash_steps_le, ``goodSign_steps_le, ``badHash_steps_le, ``badSign_steps_le,
      ``goodHash_native, ``goodSign_native, ``badHash_native, ``badSign_native,
      ``goodSimulation_bound, ``badSimulation_bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
