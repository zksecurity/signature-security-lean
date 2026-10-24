import Proofs.Runtime.BackendCoronSolver

/-! Exact law of the complete native solver. First relate it to the bounded
reference runner, including its explicit cutoff. Caller termination and the
source-program correspondence then identify the named lazy Coron co-CDH solver.
This semantic bridge does not transfer the reference runner's runtime labels. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeSolver

open BackendProgram

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
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁))
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

theorem caller_reference_denote (sampling : Machine.SamplingCosts) (qS fuel : Nat) (pk : G₂)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    (NativeHandler.caller rep bd ports sampler data samplingCode cost primitive R qS fuel).denote (pk, saved) =
      (fun p => (p.1.value, p.2)) <$>
        ((GeneralCaller.run R (generalHandler (F := F) (G₂ := G₂) cost sampling qS randomBound) fuel pk).run saved) := by
  rw [NativeHandler.caller_denote rep bd ports sampler data samplingCode cost primitive R sampling]
  have h := congrArg (fun computation => computation.run saved)
    (GeneralCaller.runFrom_erase R (generalHandler (F := F) (G₂ := G₂) cost sampling qS randomBound)
      fuel (R.machine.init pk))
  rw [GeneralCaller.denoteFrom_eq_runWith] at h
  simp only [runWithInput, GeneralCaller.run, bind_pure_comp, StateT.run_map, Functor.map_map] at h ⊢
  exact h.symm

omit QO QD OC [C.HasOption] in
theorem finish_reference_denote (sampling : Machine.SamplingCosts) (qS : Nat) (out : M × G₁)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    Prod.fst <$> (backendFinish rep data samplingCode cost primitive qS).denote (out, saved) =
      (fun p => p.1.value) <$>
        (((machineFinish qS).run (arithmetic F G₁ G₂ M M cost)
          (Machine.effects sampling (machineStore qS)) (out, ())).run saved) := by
  rw [backendFinish, MachineCompiler.unary_denote rep data samplingCode cost primitive sampling]
  simp only [Functor.map_map]

theorem program_reference_denote (sampling : Machine.SamplingCosts) (qS fuel : Nat)
    (g : G₁) (g₂ : G₂) (X : G₁) (pk : G₂) (h : G₁) :
    (program rep bd ports sampler boundary data samplingCode cost primitive R qS fuel).denote (g, g₂, X, pk, h, ()) =
      Run.value <$> generalSolverRun (F := F) R cost sampling g X h pk qS fuel := by
  rw [program_denote, caller_reference_denote rep bd ports sampler data samplingCode cost primitive R sampling,
    bind_map_left]
  simp only [generalSolverRun, Functor.map_map, generalReduction, map_bind]
  congr 1
  funext p
  rw [terminal_denote]
  cases hv : p.1.value with
  | none => simp
  | some out =>
      simp only [bind_pure_comp, Functor.map_map]
      exact finish_reference_denote rep data samplingCode cost primitive sampling qS out p.2

/-- The actual complete native program realizes the named co-CDH solver at
every challenge. Its arbitrary caller is identified independently of reduction
code and is proved to terminate through the selected query-fuel bound. -/
theorem program_denote_original (sampling : Machine.SamplingCosts) (qS fuel : Nat)
    (sourceProgram : G₂ → OracleComp (generalSpec M G₁ randomBound) (M × G₁))
    (hprogram : R.machine.ImplementsWithin sourceProgram fuel)
    (adv : BLS.ROM.AdversaryPK M G₁ G₂)
    (hsource : ∀ pk, simulateQ (generalSource randomBound) (sourceProgram pk) = adv pk)
    (g : G₁) (g₂ : G₂) (X : G₁) (pk : G₂) (h : G₁) :
    (program rep bd ports sampler boundary data samplingCode cost primitive R qS fuel).denote (g, g₂, X, pk, h, ()) =
      BLS.CoCDH.coronReductionLazyPK (F := F) qS (BLS.ROM.cacheForgeryPK adv) g g₂ X pk h := by
  rw [program_reference_denote rep bd ports sampler boundary data samplingCode cost primitive R sampling]
  exact generalSolverRun_erase R cost sampling g X h g₂ pk qS fuel sourceProgram hprogram adv (hsource pk)

theorem program_erase_original (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (sampling : Machine.SamplingCosts) (qS fuel : Nat)
    (sourceProgram : G₂ → OracleComp (generalSpec M G₁ randomBound) (M × G₁))
    (hprogram : R.machine.ImplementsWithin sourceProgram fuel)
    (adv : BLS.ROM.AdversaryPK M G₁ G₂)
    (hsource : ∀ pk, simulateQ (generalSource randomBound) (sourceProgram pk) = adv pk)
    (g : G₁) (g₂ : G₂) (X : G₁) (pk : G₂) (h : G₁) :
    Run.value <$> (program rep bd ports sampler boundary data samplingCode cost primitive R qS fuel).run
      control queryCost (g, g₂, X, pk, h, ()) =
        BLS.CoCDH.coronReductionLazyPK (F := F) qS (BLS.ROM.cacheForgeryPK adv) g g₂ X pk h := by
  rw [Code.run_erase]
  exact program_denote_original rep bd ports sampler boundary data samplingCode cost primitive R sampling
    qS fuel sourceProgram hprogram adv hsource g g₂ X pk h

end Signatures.Runtime.Coron.NativeSolver
