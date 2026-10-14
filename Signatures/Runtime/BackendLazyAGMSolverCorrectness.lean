import Signatures.Runtime.BackendLazyAGMSolver
import Signatures.Runtime.LazyAGMExtractionQueries

/-! Exact source correspondence of the complete native AGM solvers. Arbitrary
caller code is identified by its oracle semantics and bounded termination. The
tuple output adapter preserves the algebraic output; the shared private cache
passes from adaptive simulation into extraction without resampling. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.LazyAGM.NativeSolver

open BackendProgram Coron NativeHandler

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂
    ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M)))
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

variable (fuel : Nat)
  (sourceProgram : G₂ → OracleComp (generalSpec M G₁ randomBound)
    ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M)))
  (hprogram : R.machine.ImplementsWithin sourceProgram fuel)
  (adv : Adversary F M M G₁ G₂)
  (hsource : ∀ pk, AGM.outputView <$> simulateQ (generalSource randomBound) (sourceProgram pk) = adv.main pk)

include hprogram hsource

theorem goodProgram_source (g X : G₁) (g₂ pk : G₂) :
    (goodProgram rep bd ports sampler boundary data cost primitive sampling R fuel).denote (g, X, g₂, pk, ()) =
      BLS.LazyAGM.Reduction.goodReductionList adv g X g₂ pk := by
  have hrun := listRun (fun rho : F => rho • g) (fun rho => rho • X) adv pk
  rw [← hsource pk, simulateQ_map, StateT.run_map, Functor.map_map] at hrun
  have hjoin := congrArg
    (fun computation : ProbComp ((Output F M × Transcript M M G₁) × List (M × F)) =>
      computation >>= fun p => Prod.fst <$>
        (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F))
          (goodFinish p.1.1 p.1.2)).run p.2) hrun
  rw [goodProgram_denote, goodCaller_source rep bd ports sampler data cost primitive sampling R
    fuel sourceProgram hprogram pk g X ([], ([], [])), bind_map_left]
  conv_lhs =>
    arg 2
    intro p
    rw [terminal_denote]
    dsimp only
    rw [backendExtractGood_source]
  change _ = Prod.fst <$>
    (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F))
      (BLS.LazyAGM.Reduction.goodProgram g X pk adv)).run []
  rw [goodProgram_finish, simulateQ_bind, StateT.run_bind, map_bind]
  simpa only [observe, bind_map_left] using hjoin

theorem badProgram_source (g X : G₁) (g₂ pk : G₂) :
    (badProgram rep bd ports sampler boundary data cost primitive sampling R fuel).denote (g, X, g₂, pk, ()) =
      BLS.LazyAGM.Reduction.badReductionList adv g X g₂ pk := by
  rw [badProgram_denote, BLS.LazyAGM.Reduction.badReductionList]
  apply bind_congr
  intro kappa
  have hrun := listRun (fun masks : F × F => masks.1 • X + masks.2 • g)
    (fun masks => kappa • (masks.1 • X + masks.2 • g)) adv (kappa • g₂)
  rw [← hsource (kappa • g₂), simulateQ_map, StateT.run_map, Functor.map_map] at hrun
  have hjoin := congrArg
    (fun computation : ProbComp ((Output F M × Transcript M M G₁) × List (M × (F × F))) =>
      computation >>= fun p => Prod.fst <$>
        (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × F))
          (badFinish p.1.1 p.1.2)).run p.2) hrun
  rw [badCaller_source rep bd ports sampler data cost primitive sampling R
    fuel sourceProgram hprogram (kappa • g₂) g X kappa ([], ([], [])), bind_map_left]
  conv_lhs =>
    arg 2
    intro p
    rw [terminal_denote]
    dsimp only
    rw [backendExtractBad_source]
  change _ = Prod.fst <$>
    (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × F))
      (BLS.LazyAGM.Reduction.badProgram g X (kappa • g₂) kappa adv)).run []
  rw [badProgram_finish, simulateQ_bind, StateT.run_bind, map_bind]
  simpa only [observe, bind_map_left] using hjoin

omit hprogram in
theorem goodProgram_source_of_resources (bound : ExecutionCost)
    (hrun : R.RunsWithin (fun _ => bound)) (hfuel : bound.queries ≤ fuel)
    (hrealizes : R.machine.Implements sourceProgram) (g X : G₁) (g₂ pk : G₂) :
    (goodProgram rep bd ports sampler boundary data cost primitive sampling R fuel).denote (g, X, g₂, pk, ()) =
      BLS.LazyAGM.Reduction.goodReductionList adv g X g₂ pk :=
  goodProgram_source rep bd ports sampler boundary data cost primitive sampling R fuel sourceProgram
    (GeneralCaller.implementsWithin_of_resources R bound hrun sourceProgram hrealizes fuel hfuel) adv hsource g X g₂ pk

omit hprogram in
theorem badProgram_source_of_resources (bound : ExecutionCost)
    (hrun : R.RunsWithin (fun _ => bound)) (hfuel : bound.queries ≤ fuel)
    (hrealizes : R.machine.Implements sourceProgram) (g X : G₁) (g₂ pk : G₂) :
    (badProgram rep bd ports sampler boundary data cost primitive sampling R fuel).denote (g, X, g₂, pk, ()) =
      BLS.LazyAGM.Reduction.badReductionList adv g X g₂ pk :=
  badProgram_source rep bd ports sampler boundary data cost primitive sampling R fuel sourceProgram
    (GeneralCaller.implementsWithin_of_resources R bound hrun sourceProgram hrealizes fuel hfuel) adv hsource g X g₂ pk

end Signatures.Runtime.LazyAGM.NativeSolver
