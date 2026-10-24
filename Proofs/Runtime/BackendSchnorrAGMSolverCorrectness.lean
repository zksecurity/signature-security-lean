import Proofs.Runtime.BackendSchnorrAGMSolver

/-! The assembled native solver exactly realizes the named finite-list DLog
reduction. The caller may use arbitrary backend code; its measured query bound
and semantic implementation law justify termination and the source connection. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Solver

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [QD : Q.IsDistributive] [Q.HasOption] [OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [DecidableEq (SourceRequest F G₁ M)]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor (SourceInput G₁) (SourceForgery F G₁ M))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (ports : Ports (Q := Q) rep bd)
  (randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

theorem program_source_of_resources (hsample : sampler.denote () = ($ᵗ F : ProbComp F))
    (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
    (fuel : Nat) (hfuel : bound.queries ≤ fuel)
    (adv : Schnorr.AGM.Adversary F G₁ M) (hprogram : R.machine.Implements adv.main)
    (g pk : G₁) :
    (program rep bd boundary data cost primitive ports randomPorts sampler R fuel).denote (g, pk, ()) =
      dlogReduction adv g pk := by
  rw [program_denote,
    Handler.caller_source_of_resources rep bd ports data cost primitive randomPorts sampler R bound hrun
      hsample fuel hfuel adv.main hprogram (Schnorr.AGM.initial g pk) g pk ({} : State F G₁ M),
    bind_map_left, dlogReduction_finishScalar]
  simp only [StateT.run_bind, map_bind]
  congr 1
  funext p
  rw [terminal_denote]
  dsimp only
  rw [Extraction.source rep data cost primitive sampler hsample]
  simp only [Functor.map_map]

end Signatures.Runtime.SchnorrAGM.Native.Solver
