import Proofs.Runtime.BackendLazyAGMSolver

/-! Size and local-time contracts for the actual solver boundary conversions.
Output decoding controls the entire representation, including surplus
coefficients. No complete solver or extraction cost is supplied here. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.LazyAGM.NativeSolver

open BackendProgram Coron

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂
    ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M)))
  (boundary : DataPorts (Q := Q) rep bd)

structure PortCaps (keyWidth outputWidth routeWidth adapterTime : Nat) : Prop where
  key : ∀ pk, Q.size (rep.ty point₂) pk ≤ keyWidth →
    Q.size bd.input pk ≤ routeWidth ∧ Q.cost boundary.key pk ≤ adapterTime
  output : ∀ out, Q.size bd.out out ≤ routeWidth →
    Q.size (rep.ty (AGM.outputTy message)) out ≤ outputWidth ∧ Q.cost boundary.output out ≤ adapterTime
  optional : ∀ result, (∀ out, result = some out → Q.size bd.out out ≤ routeWidth) →
    Q.cost boundary.optional result ≤ adapterTime

def ResultReady (routeWidth : Nat)
    (result : Option ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))) : Prop :=
  ∀ out, result = some out → Q.size bd.out out ≤ routeWidth

end Signatures.Runtime.LazyAGM.NativeSolver
