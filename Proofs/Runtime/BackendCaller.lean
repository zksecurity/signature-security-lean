import Proofs.Runtime.BackendAssembly
import Proofs.Runtime.GeneralCaller

/-! Assemble a general caller and a finite handler program in one backend.

Only local caller code and structural backend code enter atomic nodes. Every
handler invocation uses the supplied finite `Code`, whose only external effects
are those of the target interface. The same loop body is reused for every query.
-/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}

/-- The two remaining optional-value wiring operations, with executable code
in the same backend and the pinned optional/product representations. -/
class OptionCode where
  someCode : ∀ {A : Type} (a : C.Str A), Q.Realizer a (StepClass.HasOption.option a) some
  getDCode : ∀ {A : Type} (a : C.Str A),
    Q.Realizer (StepClass.HasProd.prod (StepClass.HasOption.option a) a) a
      (fun input => input.1.getD input.2)

namespace Caller

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {I A B S J : Type} {source : OracleSpec I} [DecidableEq I]
  {bd : Boundary C source.toPFunctor A B}
  (R : GeneralCaller.Caller (Q := Q) (bd := bd)) (store : C.Str S)
  {target : OracleSpec J} {iface : Interface (C := C) target}

abbrev frame := StepClass.HasProd.prod R.state store
abbrev result := StepClass.HasProd.prod (StepClass.HasOption.option bd.out) store

def inspectCode : Q.Realizer (frame R store)
    (StepClass.HasSum.sum (StepClass.HasProd.prod bd.out (frame R store))
      (StepClass.HasProd.prod bd.pos (frame R store)))
    (fun input => Sum.elim (fun value => Sum.inl (value, input))
      (fun position => Sum.inr (position, input)) (R.machine.head input.1)) :=
  Q.compose (QP.pair (Q.compose (QP.fst R.state store) R.headCode) (Q.identity (frame R store)))
    (QD.distribute bd.out bd.pos (frame R store))

def doneCode : Q.Realizer (StepClass.HasProd.prod bd.out (frame R store)) (result (bd := bd) store)
    (fun input => (some input.1, input.2.2)) :=
  QP.pair (Q.compose (QP.fst bd.out (frame R store)) (OC.someCode bd.out))
    (Q.compose (QP.snd bd.out (frame R store)) (QP.snd R.state store))

def queryArgsCode : Q.Realizer (StepClass.HasProd.prod bd.pos (frame R store))
    (StepClass.HasProd.prod (StepClass.HasProd.prod bd.pos store) R.state)
    (fun input => ((input.1, input.2.2), input.2.1)) :=
  QP.pair (QP.pair (QP.fst bd.pos (frame R store))
      (Q.compose (QP.snd bd.pos (frame R store)) (QP.snd R.state store)))
    (Q.compose (QP.snd bd.pos (frame R store)) (QP.fst R.state store))

def resumeArgsCode : Q.Realizer (StepClass.HasProd.prod (StepClass.HasProd.prod bd.idx store) R.state)
    (StepClass.HasProd.prod (bd.stateIdx R.state) store)
    (fun input => ((input.2, input.1.1), input.1.2)) :=
  QP.pair (QP.pair (QP.snd (StepClass.HasProd.prod bd.idx store) R.state)
      (Q.compose (QP.fst (StepClass.HasProd.prod bd.idx store) R.state) (QP.fst bd.idx store)))
    (Q.compose (QP.fst (StepClass.HasProd.prod bd.idx store) R.state) (QP.snd bd.idx store))

/-- The default is the previous state. A matching handler reply makes the
update enabled, so correctness proves that this default is never selected. -/
def updateCode : Q.Realizer (bd.stateIdx R.state) R.state
    (fun input => (R.machine.update? input).getD input.1) :=
  Q.compose (QP.pair R.updateCode (QP.fst R.state bd.idx)) (OC.getDCode R.state)

def cutoffCode : Q.Realizer (StepClass.HasProd.prod bd.pos (frame R store)) (result (bd := bd) store)
    (fun input => (none, input.2.2)) :=
  QP.pair (QO.none (StepClass.HasProd.prod bd.pos (frame R store)) bd.out)
    (Q.compose (QP.snd bd.pos (frame R store)) (QP.snd R.state store))

variable (handler : Code Q target iface (StepClass.HasProd.prod bd.pos store)
  (StepClass.HasProd.prod bd.idx store))

def body : Code Q target iface (frame R store)
    (StepClass.HasSum.sum (result (bd := bd) store) (frame R store)) :=
  .seq (.atomic (inspectCode R store))
    (.branch
      (.seq (.atomic (doneCode R store))
        (.atomic (QS.inl (result (bd := bd) store) (frame R store))))
      (.seq (.atomic (queryArgsCode R store))
        (.seq (.first R.state handler)
          (.seq (.atomic (resumeArgsCode R store))
            (.seq (.first store (.atomic (updateCode R)))
              (.atomic (QS.inr (result (bd := bd) store) (frame R store))))))))

def stop : Code Q target iface (frame R store) (result (bd := bd) store) :=
  .seq (.atomic (inspectCode R store))
    (.branch (.atomic (doneCode R store)) (.atomic (cutoffCode R store)))

def fromState (fuel : Nat) : Code Q target iface (frame R store) (result (bd := bd) store) :=
  .loop (body R store handler) (stop R store) fuel

def program (fuel : Nat) : Code Q target iface
    (StepClass.HasProd.prod bd.input store) (result (bd := bd) store) :=
  .seq (.first store (.atomic R.initCode)) (fromState R store handler fuel)

/-- All static caller/routing descriptions, apart from the handler and fuel.
This includes embedded caller initialization/head/update code through the actual
backend realizers, rather than treating an attacker callback as a unit-size token. -/
def wiringDescriptionSize (sizes : DescriptionSize Q) : Nat :=
  sizes.localSize R.initCode + 2 * sizes.localSize (inspectCode R store) +
    2 * sizes.localSize (doneCode R store) + sizes.localSize (queryArgsCode R store) +
    sizes.localSize (resumeArgsCode R store) + sizes.localSize (updateCode R) +
    sizes.localSize (cutoffCode R store) +
    sizes.localSize (QS.inl (result (bd := bd) store) (frame R store)) +
    sizes.localSize (QS.inr (result (bd := bd) store) (frame R store)) + 26

theorem program_descriptionSize (sizes : DescriptionSize Q) (fuel : Nat) :
    (program R store handler fuel).descriptionSize sizes =
      wiringDescriptionSize R store sizes + handler.descriptionSize sizes + fuel := by
  dsimp [program, fromState, body, stop, Code.descriptionSize, wiringDescriptionSize]
  omega

end Caller
end Signatures.Runtime.BackendProgram
