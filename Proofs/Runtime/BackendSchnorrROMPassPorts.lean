import Proofs.Runtime.BackendSchnorrROMPass

/-! Local contracts for the actual pass boundary conversions. Caller and native
representations may differ; all conversion code is executed and charged. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativePass

open BackendProgram NativeInterface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C} {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : DataPorts (Q := Q) rep bd)

def ResultReady (outputWidth : Nat) (result : Option (M × G₁ × F)) : Prop :=
  ∀ out, result = some out → Q.size bd.out out ≤ outputWidth

structure PortCaps (width routeWidth outputWidth inputTime outputTime optionalTime : Nat) : Prop where
  input : ∀ pk, Q.size (rep.ty point₁) pk ≤ width →
    Q.size bd.input pk ≤ routeWidth ∧ Q.cost boundary.input pk ≤ inputTime
  output : ∀ out, Q.size bd.out out ≤ outputWidth →
    Q.size (rep.ty forgery) out ≤ width ∧ Q.cost boundary.output out ≤ outputTime
  optional : ∀ result, ResultReady (Q := Q) bd outputWidth result →
    Q.cost boundary.optional result ≤ optionalTime

end Signatures.Runtime.Schnorr.ListROM.NativePass
