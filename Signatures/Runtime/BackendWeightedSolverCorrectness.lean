import Signatures.Runtime.BackendWeightedSolver
import Signatures.Runtime.WeightedExtraction

/-! Exact source correspondence of the complete native AGM solvers. Arbitrary
caller code is identified by its oracle semantics and bounded termination. The
tuple output adapter preserves the algebraic output; the shared private cache
passes from adaptive simulation into extraction without resampling. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM.NativeSolver

open BackendProgram NativeHandler Reply

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (index : Index)
  (bd : Boundary C (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor G₂
    ((AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M)))
  (ports : NativePorts (Q := Q) rep index.ty index.messageTy bd) (sampler : BoundedSampler rep index.ty index.messageTy bd ports (iface := iface))
  (boundary : DataPorts (Q := Q) rep index bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

attribute [local implicit_reducible] PFunctor.Idx

variable (fuel : Nat)
  (sourceProgram : G₂ → OracleComp (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound)
    ((AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M)))
  (hprogram : R.machine.ImplementsWithin sourceProgram fuel)
  (adv : Adversary F (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ G₂)
  (hsource : ∀ pk, AGM.outputView <$> simulateQ (generalSource randomBound) (sourceProgram pk) = adv.main pk)

include hprogram hsource

theorem goodProgram_source (g X : G₁) (g₂ pk : G₂) :
    (goodProgram rep index bd ports sampler boundary data cost primitive sampling R fuel).denote (g, X, g₂, pk, ()) =
      Model.LazyAGM.WeightedReduction.goodReductionList (index.sourceTerms cost) adv g X g₂ pk := by
  have hrun := listRun (index.sourceTerms cost) (fun rho : F => rho • g) (fun rho => rho • X) adv pk
  rw [← hsource pk, simulateQ_map, StateT.run_map, Functor.map_map] at hrun
  have hjoin := congrArg
    (fun computation : ProbComp ((Output F (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) × Transcript (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁) × List ((index.ty.Value (cryptoBase F G₁ G₂ K M)) × F)) =>
      computation >>= fun p => Prod.fst <$>
        (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := (index.ty.Value (cryptoBase F G₁ G₂ K M))) (R := F))
          (Extract.goodFinish (index.sourceTerms cost) p.1.1 p.1.2)).run p.2) hrun
  rw [goodProgram_denote, goodCaller_source rep index bd ports sampler data cost primitive sampling R
    fuel sourceProgram hprogram pk g X ([], ([], [])), bind_map_left]
  conv_lhs =>
    arg 2
    intro p
    rw [terminal_denote]
    dsimp only
    rw [Extract.backendGood_source]
  change _ = Prod.fst <$>
    (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := (index.ty.Value (cryptoBase F G₁ G₂ K M))) (R := F))
      (Model.LazyAGM.WeightedReduction.goodProgram (index.sourceTerms cost) g X pk adv)).run []
  rw [Extract.goodProgram_finish, simulateQ_bind, StateT.run_bind, map_bind]
  simpa only [observe, bind_map_left] using hjoin

theorem badProgram_source (g X : G₁) (g₂ pk : G₂) :
    (badProgram rep index bd ports sampler boundary data cost primitive sampling R fuel).denote (g, X, g₂, pk, ()) =
      Model.LazyAGM.WeightedReduction.badReductionList (index.sourceTerms cost) adv g X g₂ pk := by
  rw [badProgram_denote, Model.LazyAGM.WeightedReduction.badReductionList]
  apply bind_congr
  intro kappa
  have hrun := listRun (index.sourceTerms cost) (fun masks : F × F => masks.1 • X + masks.2 • g)
    (fun masks => kappa • (masks.1 • X + masks.2 • g)) adv (kappa • g₂)
  rw [← hsource (kappa • g₂), simulateQ_map, StateT.run_map, Functor.map_map] at hrun
  have hjoin := congrArg
    (fun computation : ProbComp ((Output F (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) × Transcript (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁) × List ((index.ty.Value (cryptoBase F G₁ G₂ K M)) × (F × F))) =>
      computation >>= fun p => Prod.fst <$>
        (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := (index.ty.Value (cryptoBase F G₁ G₂ K M))) (R := F × F))
          (Extract.badFinish (index.sourceTerms cost) p.1.1 p.1.2)).run p.2) hrun
  rw [badCaller_source rep index bd ports sampler data cost primitive sampling R
    fuel sourceProgram hprogram (kappa • g₂) g X kappa ([], ([], [])), bind_map_left]
  conv_lhs =>
    arg 2
    intro p
    rw [terminal_denote]
    dsimp only
    rw [Extract.backendBad_source]
  change _ = Prod.fst <$>
    (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := (index.ty.Value (cryptoBase F G₁ G₂ K M))) (R := F × F))
      (Model.LazyAGM.WeightedReduction.badProgram (index.sourceTerms cost) g X (kappa • g₂) kappa adv)).run []
  rw [Extract.badProgram_finish, simulateQ_bind, StateT.run_bind, map_bind]
  simpa only [observe, bind_map_left] using hjoin

omit hprogram in
theorem goodProgram_source_of_resources (bound : ExecutionCost)
    (hrun : R.RunsWithin (fun _ => bound)) (hfuel : bound.queries ≤ fuel)
    (hrealizes : R.machine.Implements sourceProgram) (g X : G₁) (g₂ pk : G₂) :
    (goodProgram rep index bd ports sampler boundary data cost primitive sampling R fuel).denote (g, X, g₂, pk, ()) =
      Model.LazyAGM.WeightedReduction.goodReductionList (index.sourceTerms cost) adv g X g₂ pk :=
  goodProgram_source rep index bd ports sampler boundary data cost primitive sampling R fuel sourceProgram
    (GeneralCaller.implementsWithin_of_resources R bound hrun sourceProgram hrealizes fuel hfuel) adv hsource g X g₂ pk

omit hprogram in
theorem badProgram_source_of_resources (bound : ExecutionCost)
    (hrun : R.RunsWithin (fun _ => bound)) (hfuel : bound.queries ≤ fuel)
    (hrealizes : R.machine.Implements sourceProgram) (g X : G₁) (g₂ pk : G₂) :
    (badProgram rep index bd ports sampler boundary data cost primitive sampling R fuel).denote (g, X, g₂, pk, ()) =
      Model.LazyAGM.WeightedReduction.badReductionList (index.sourceTerms cost) adv g X g₂ pk :=
  badProgram_source rep index bd ports sampler boundary data cost primitive sampling R fuel sourceProgram
    (GeneralCaller.implementsWithin_of_resources R bound hrun sourceProgram hrealizes fuel hfuel) adv hsource g X g₂ pk

end Signatures.Runtime.WeightedAGM.NativeSolver
