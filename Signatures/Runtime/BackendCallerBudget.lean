import Signatures.Runtime.BackendCallerCorrectness
import Signatures.Runtime.BackendBudget

/-! Derived execution and description bounds for the assembled caller.

Premises concern initialization, one oracle-dispatch iteration, the terminal
readout, and size-dependent control operations. They do not assume a bound for
the full execution. The component rules in `BackendBudget` discharge these local
premises from backend/primitive implementation and representation contracts.
-/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.BackendProgram.Caller

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {I A B S J : Type} {source : OracleSpec I} [DecidableEq I]
  {bd : Boundary C source.toPFunctor A B}
  (R : GeneralCaller.Caller (Q := Q) (bd := bd)) (store : C.Str S)
  {target : OracleSpec J} {iface : Interface (C := C) target}
  (handler : Code Q target iface (StepClass.HasProd.prod bd.pos store)
    (StepClass.HasProd.prod bd.idx store))
  (control : ControlCosts) (queryCost : (j : J) → target.Range j → Nat)

theorem program_bound (pre : A × S → Prop) (inv : R.machine.State × S → Prop)
    (post : Option B × S → Prop) (initTime bodyTime stopTime tickTime joinTime fuel : Nat)
    (hi : Bounds control queryCost (.first (iface := iface) store (.atomic R.initCode)) pre inv initTime)
    (hb : Bounds control queryCost (body R store handler) inv (Sum.elim post inv) bodyTime)
    (hs : Bounds control queryCost (stop (iface := iface) R store) inv post stopTime)
    (ht : ∀ count ≤ fuel, ∀ state, inv state → control.loop count (Q.size (frame R store) state) ≤ tickTime)
    (hj : ∀ input, pre input → ∀ state, inv state →
      control.sequence (Q.size (StepClass.HasProd.prod bd.input store) input)
        (Q.size (frame R store) state) ≤ joinTime) :
    Bounds control queryCost (program R store handler fuel) pre post
      (initTime + (fuel * (bodyTime + tickTime) + stopTime + tickTime) + joinTime) :=
  Bounds.seq control queryCost _ _ pre inv post _ _ _ hi
    (Bounds.loop control queryCost _ _ inv post _ _ _ _ hb hs ht) hj

theorem compiled_program_bound
    (backend : Backend.{v, w, x} Q target iface control queryCost)
    (pre : A × S → Prop) (inv : R.machine.State × S → Prop) (post : Option B × S → Prop)
    (initTime bodyTime stopTime tickTime joinTime fuel : Nat)
    (hi : Bounds control queryCost (.first (iface := iface) store (.atomic R.initCode)) pre inv initTime)
    (hb : Bounds control queryCost (body R store handler) inv (Sum.elim post inv) bodyTime)
    (hs : Bounds control queryCost (stop (iface := iface) R store) inv post stopTime)
    (ht : ∀ count ≤ fuel, ∀ state, inv state → control.loop count (Q.size (frame R store) state) ≤ tickTime)
    (hj : ∀ input, pre input → ∀ state, inv state →
      control.sequence (Q.size (StepClass.HasProd.prod bd.input store) input)
        (Q.size (frame R store) state) ≤ joinTime)
    (input : A × S) (hp : pre input) (z : Run (Option B × S))
    (hz : z ∈ support (backend.execute (backend.compile (program R store handler fuel)) input)) :
    post z.value ∧ z.steps ≤ initTime + (fuel * (bodyTime + tickTime) + stopTime + tickTime) + joinTime := by
  rw [backend.compile_execute] at hz
  exact program_bound R store handler control queryCost pre inv post
    initTime bodyTime stopTime tickTime joinTime fuel hi hb hs ht hj input hp z hz

theorem compiled_program_descriptionSize
    (backend : Backend.{v, w, x} Q target iface control queryCost)
    (sizes : DescriptionSize Q) (factor : Nat) (description : backend.DescriptionBound sizes factor)
    (fuel : Nat) :
    description.size (backend.compile (program R store handler fuel)) ≤
      factor * (wiringDescriptionSize R store sizes + handler.descriptionSize sizes + fuel) := by
  simpa only [program_descriptionSize] using
    backend.compile_descriptionSize sizes factor description (program R store handler fuel)

end Signatures.Runtime.BackendProgram.Caller
