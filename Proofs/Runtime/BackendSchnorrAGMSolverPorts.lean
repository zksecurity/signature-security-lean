import Proofs.Runtime.BackendSchnorrAGMSolver

/-! Local representation contracts for the executed solver ports. Source and
native output widths are separate; complete reduction budgets are not premises. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Solver

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor (SourceInput G₁) (SourceForgery F G₁ M))
  (boundary : DataPorts (Q := Q) rep bd)

def ResultReady (routeWidth : Nat) (result : Option (SourceForgery F G₁ M)) : Prop :=
  ∀ out, result = some out → Q.size bd.out out ≤ routeWidth

structure PortCaps (width outputWidth routeWidth adapterTime : Nat) : Prop where
  input : ∀ config, Q.size (rep.ty configTy) config ≤ 3 * width →
    Q.size bd.input (Schnorr.AGM.initial config.1 config.2) ≤ routeWidth ∧
      Q.cost boundary.input config ≤ adapterTime
  output : ∀ out, Q.size bd.out out ≤ routeWidth →
    Q.size (rep.ty forgeryTy) (encodeForgery out) ≤ outputWidth ∧ Q.cost boundary.output out ≤ adapterTime
  optional : ∀ result, ResultReady (Q := Q) bd routeWidth result →
    Q.cost boundary.optional result ≤ adapterTime

end Signatures.Runtime.SchnorrAGM.Native.Solver
