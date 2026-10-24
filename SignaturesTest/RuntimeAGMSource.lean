import Signatures.BLS.Statement
import Signatures.OOPS.Statement
import Signatures.Proximity.Statement
import Proofs.Runtime.AGMBadMachine
import Proofs.Runtime.KeyEquality
import Proofs.Runtime.ProximityWeight
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open Signatures.Runtime OracleComp OracleSpec

namespace SignaturesTest.RuntimeAGMSource

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5
private def cost := PrimitiveCosts.unit
private def sampling : Machine.SamplingCosts := ⟨1, fun _ => 1⟩
private abbrev primitives := arithmetic F F F Bool Unit cost
private def output : (AGM.outputTy key).Value (cryptoBase F F F Bool Unit) := (false, 2, [1, 2], [])
private def queries : Fin 3 → Nat := ![0, 1, 0]

private def code : Program CryptoOp (AGM.Command key key 0)
    [point₂, AGM.outputTy key] (AGM.outputTy key) :=
  .bind (.query .hash (.fst (.var (.there .here))))
    (.ret (.var (.there (.there .here))))

private def adversary : Model.LazyAGM.Adversary F Bool Bool F F where
  main _ := do
    let _ ← (liftM ((Model.LazyAGM.advSpec Bool Bool F).query (.inl (.inr false))) :
      OracleComp (Model.LazyAGM.advSpec Bool Bool F) F)
    pure ⟨false, 2, [1, 2], []⟩

private def cert : AGM.SourceCertificate (F := F) (G₁ := F) (G₂ := F) (K := Bool) (M := Unit)
    (indexTy := key) (messageTy := key) cost (Equiv.refl Bool) (Equiv.refl Bool) 0 9 queries 2 0 adversary where
  dataTy := AGM.outputTy key
  data := output
  code := code
  semantics pk := by
    simp [code, Program.denote, Expr.denote, Var.get, output, AGM.decodeOutput,
      AGM.sourceSemantics, adversary]
  budget pk := by
    intro price z hz
    simp only [code, Program.run, Expr.run, Var.get, Var.depth, pricedRequests,
      bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨r, _, rfl⟩ := hz
    simp [AGM.kind, queries, Fin.sum_univ_succ]
    omega
  outputSizes pk price z hz := by
    simp only [code, Program.run, Expr.run, Var.get, Var.depth, pricedRequests,
      bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨r, _, rfl⟩ := hz
    simp [output]

example (pk : F) : SourceBudget primitives (AGM.replies 0) AGM.kind code (pk, output, ()) 9 queries :=
  cert.budget pk

-- A source cannot hide an oversized algebraic output behind a valid query budget.
example : ¬ (∀ (pk : F) (price : Fin 3 → Nat) z,
    z ∈ support (code.run primitives
      (pricedRequests (AGM.replies 0) (fun cmd => price (AGM.kind cmd))) (pk, output, ())) →
    z.value.2.2.1.length ≤ 1) := by
  intro h
  have hz : (⟨output, 9⟩ : Run ((AGM.outputTy key).Value (cryptoBase F F F Bool Unit))) ∈
      support (code.run primitives (pricedRequests (AGM.replies 0) (fun _ => 0)) (0, output, ())) := by
    simp only [code, Program.run, Expr.run, Var.get, Var.depth, pricedRequests,
      bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
    exact ⟨⟨0, trivial⟩, mem_support_query _ _, trivial⟩
  have hb := h 0 (fun _ => 0) ⟨output, 9⟩ hz
  norm_num [output] at hb

private def constantCode : Program CryptoOp (AGM.Command key key 0)
    [point₂, AGM.outputTy key] (AGM.outputTy key) := .ret (.var (.there .here))

-- Agreement at one public key is insufficient for the all-key semantic certificate.
example : ¬ (∀ pk : F,
    AGM.decodeOutput (Equiv.refl Bool) <$>
      constantCode.denote primitives (AGM.sourceSemantics (Equiv.refl Bool) (Equiv.refl Bool) 0)
        (pk, output, ()) =
      (pure ⟨false, pk, [1, 2], []⟩ : OracleComp (Model.LazyAGM.advSpec Bool Bool F)
        (Model.LazyAGM.Output F Bool))) := by
  intro h
  have hz := h 0
  have he : (⟨false, (2 : F), [1, 2], []⟩ : Model.LazyAGM.Output F Bool) = ⟨false, 0, [1, 2], []⟩ := by
    simpa [constantCode, Program.denote, Expr.denote, Var.get, output, AGM.decodeOutput] using hz
  have hb := congrArg Model.LazyAGM.Output.β he
  exact (by decide : (2 : F) ≠ 0) hb

example : AGM.goodExecutionBound cost sampling 0 9 2 queries 2 0 6 10 = 930 := by
  norm_num [AGM.goodExecutionBound, AGM.machinePrices, AGM.goodHashBound, AGM.goodSignBound,
    AGM.goodExtractBound, AGM.tokenRowsBound, AGM.goodCoreBound, AGM.baseCoefficientBound,
    AGM.denominatorWeightBound, queries, cost, sampling, PrimitiveCosts.unit, Fin.sum_univ_succ]

example : AGM.badExecutionBound cost sampling 0 9 2 2 2 queries 0 6 10 = 824 := by
  norm_num [AGM.badExecutionBound, AGM.machinePrices, AGM.badHashBound, AGM.badSignBound,
    AGM.badExtractBound, AGM.tokenRowsBound, AGM.badCoreBound,
    AGM.denominatorWeightBound, queries, cost, sampling, PrimitiveCosts.unit, Fin.sum_univ_succ]

-- Complete good-branch source, setup, full-domain sampling, execution, and extraction budget.
example : cert.goodBudget sampling 6 10 = 1334 := by
  simp [AGM.SourceCertificate.goodBudget, AGM.goodCodeBound, AGM.sampleKeyedBound,
    AGM.goodExecutionBound, AGM.machinePrices, AGM.goodHashBound, AGM.goodSignBound,
    AGM.goodExtractBound, AGM.tokenRowsBound, AGM.goodCoreBound, AGM.baseCoefficientBound,
    AGM.denominatorWeightBound, cert, queries, output, cost, sampling, PrimitiveCosts.unit,
    Fin.sum_univ_succ, Env.load, Ty.load, AGM.canonicalKeys]

example : AGM.dlogWithin (F := F) (K := Bool) (M := Unit) cost sampling (cert.goodBudget sampling 6 10)
    (Model.LazyAGM.goodReduction BLS.Proofs.indicatorWeight adversary) := by
  exact cert.goodWithin sampling AGM.KeyEquality.bls (fun x y => AGM.KeyEquality.bls_value cost x y)
    Weights.bls BLS.Proofs.indicatorWeight (fun i m => Weights.bls_value cost i m) 6 10
    (fun x y => le_of_eq (AGM.KeyEquality.bls_steps cost x y))
    (fun i m => le_of_eq (Weights.bls_steps cost i m))

example (g X g₂ pk : F) :
    Run.value <$> (cert.goodPackage AGM.KeyEquality.bls Weights.bls).run cost sampling (g, X, g₂, pk, ()) =
      Model.LazyAGM.goodReduction BLS.Proofs.indicatorWeight adversary g X g₂ pk := by
  rw [Machine.Package.run_eq]
  simp only [Functor.map_map]
  exact cert.goodCode_erase sampling AGM.KeyEquality.bls (fun x y => AGM.KeyEquality.bls_value cost x y)
    Weights.bls BLS.Proofs.indicatorWeight (fun i m => Weights.bls_value cost i m) g X g₂ pk

-- The bad budget includes kappa, two complete tables, masked bases, and public-key construction.
example : cert.badBudget sampling 6 10 = 1932 := by
  simp [AGM.SourceCertificate.badBudget, AGM.badCodeBound, AGM.sampleKeyedBound,
    AGM.maskedBasesBound, AGM.pairTablesBound,
    AGM.badExecutionBound, AGM.machinePrices, AGM.badHashBound, AGM.badSignBound,
    AGM.badExtractBound, AGM.tokenRowsBound, AGM.badCoreBound, AGM.denominatorWeightBound,
    cert, queries, output, cost, sampling, PrimitiveCosts.unit,
    Fin.sum_univ_succ, Env.load, Ty.load, AGM.canonicalKeys]

-- Increasing the scalar draw price charges all 2*N+1 draws, not just the source queries.
example : cert.badBudget ⟨2, fun _ => 1⟩ 6 10 = 1937 := by
  simp [AGM.SourceCertificate.badBudget, AGM.badCodeBound, AGM.sampleKeyedBound,
    AGM.maskedBasesBound, AGM.pairTablesBound,
    AGM.badExecutionBound, AGM.machinePrices, AGM.badHashBound, AGM.badSignBound,
    AGM.badExtractBound, AGM.tokenRowsBound, AGM.badCoreBound, AGM.denominatorWeightBound,
    cert, queries, output, cost, PrimitiveCosts.unit,
    Fin.sum_univ_succ, Env.load, Ty.load, AGM.canonicalKeys]

example : AGM.dlogWithin (F := F) (K := Bool) (M := Unit) cost sampling (cert.badBudget sampling 6 10)
    (Model.LazyAGM.badReduction BLS.Proofs.indicatorWeight adversary) := by
  exact cert.badWithin sampling AGM.KeyEquality.bls (fun x y => AGM.KeyEquality.bls_value cost x y)
    Weights.bls BLS.Proofs.indicatorWeight (fun i m => Weights.bls_value cost i m) 6 10
    (fun x y => le_of_eq (AGM.KeyEquality.bls_steps cost x y))
    (fun i m => le_of_eq (Weights.bls_steps cost i m))

example (g X g₂ X₂ : F) :
    Run.value <$> (cert.badPackage AGM.KeyEquality.bls Weights.bls).run cost sampling (g, X, g₂, X₂, ()) =
      Model.LazyAGM.badReduction BLS.Proofs.indicatorWeight adversary g X g₂ X₂ := by
  rw [Machine.Package.run_eq]
  simp only [Functor.map_map]
  exact cert.badCode_erase sampling AGM.KeyEquality.bls (fun x y => AGM.KeyEquality.bls_value cost x y)
    Weights.bls BLS.Proofs.indicatorWeight (fun i m => Weights.bls_value cost i m) g X g₂ X₂

-- Pairing follows the first table's order, not the second table's list positions.
example : ((AGM.pairTables AGM.KeyEquality.bls).run primitives
    ([(false, 2), (true, 4)], [(true, 1), (false, 3)], ())).value =
      [((false, 2), 3), ((true, 4), 1)] := by
  rw [AGM.pairTables_value cost AGM.KeyEquality.bls (fun x y => AGM.KeyEquality.bls_value cost x y)]
  decide

-- The first matching zero is retained; an absent key receives the explicit zero default.
example : ((AGM.pairTables AGM.KeyEquality.bls).run primitives
    ([(false, 2), (true, 4)], [(false, 0), (false, 3)], ())).value =
      [((false, 2), 0), ((true, 4), 0)] := by
  rw [AGM.pairTables_value cost AGM.KeyEquality.bls (fun x y => AGM.KeyEquality.bls_value cost x y)]
  decide

example : ((AGM.maskedBases AGM.KeyEquality.bls).run primitives
    (1, 2, [(false, 2), (true, 4)], [(true, 1), (false, 3)], ())).value =
      [(false, 2), (true, 4)] := by
  rw [AGM.maskedBases_run]
  simp only [AGM.pairTables_value cost AGM.KeyEquality.bls
    (fun x y => AGM.KeyEquality.bls_value cost x y)]
  decide

example (z : Run (List (Bool × F)) × Nat)
    (hz : z ∈ support (((AGM.sampleKeyed (indexTy := key) .nat 2).run primitives (Machine.effects sampling .nat)
      ([false, true], ())).run 7)) :
    z.2 = 7 ∧ z.1.value.length = 2 ∧ z.1.steps ≤ 320 :=
  AGM.sampleKeyed_bound (indexTy := key) (G₁ := F) (G₂ := F) (K := Bool) (M := Unit)
    cost sampling .nat 2 [false, true] 7 z hz

-- Empty-domain initialization still executes the sampler, constructor, and frames.
example (z : Run (List (Bool × F)) × Nat)
    (hz : z ∈ support (((AGM.sampleKeyed (indexTy := key) .nat 0).run primitives (Machine.effects sampling .nat)
      ([], ())).run 7)) :
    z.2 = 7 ∧ z.1.value.length = 0 ∧ z.1.steps ≤ 42 :=
  AGM.sampleKeyed_bound (indexTy := key) (G₁ := F) (G₂ := F) (K := Bool) (M := Unit)
    cost sampling .nat 0 [] 7 z hz

end SignaturesTest.RuntimeAGMSource

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``AGM.machineSimulation_supported, ``AGM.SourceCertificate.simulated_output_sizes,
      ``AGM.SourceCertificate.simulation_erase, ``AGM.goodExtractBound_mono, ``AGM.badExtractBound_mono,
      ``AGM.goodExecution_run, ``AGM.badExecution_run, ``AGM.SourceCertificate.goodExecution_bound,
      ``AGM.SourceCertificate.badExecution_bound, ``AGM.baseCoeff_decode, ``AGM.denominatorCoeff_decode,
      ``AGM.goodExtract_native, ``AGM.badExtract_native, ``AGM.SourceCertificate.goodSimulation_erase,
      ``AGM.SourceCertificate.badSimulation_erase, ``AGM.SourceCertificate.goodExecution_erase,
      ``AGM.SourceCertificate.badExecution_erase, ``AGM.keyedValues_run, ``AGM.keyedValues_value,
      ``AGM.sampleKeyed_run, ``AGM.sampleKeyed_bound, ``AGM.sampleKeyed_native,
      ``AGM.goodCode_run, ``AGM.SourceCertificate.goodCode_bound, ``AGM.SourceCertificate.goodCode_erase,
      ``AGM.SourceCertificate.goodWithin, ``AGM.sampleKeyed_bind_native,
      ``AGM.pairTablesBody_run, ``AGM.pairTables_value, ``AGM.pairTables_length,
      ``AGM.pairTables_steps_le, ``AGM.pairTables_native, ``AGM.maskedBases_run,
      ``AGM.maskedBases_length, ``AGM.maskedBases_steps_le, ``AGM.maskedBases_native,
      ``AGM.badCode_run, ``AGM.SourceCertificate.badCode_bound, ``AGM.SourceCertificate.badCode_erase,
      ``AGM.SourceCertificate.badWithin,
      ``BLS.agm_security, ``OOPS.agm_security, ``Proximity.agm_security] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
