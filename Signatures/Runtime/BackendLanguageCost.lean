import Signatures.Runtime.BackendExpressionCost
import Signatures.Runtime.BackendLanguage
import Signatures.Runtime.BackendBudget

/-! Bounds for the actual local adapters emitted by the state-passing compiler.
The certificates are built from primitive and encoded-size structural contracts,
including the expression compiler's derived bounds. No complete adapter runtime
is assumed. Effectful sequencing and iteration use the rules in `BackendBudget`.
-/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}

/-- Discharge an atomic assembly rule with a constructed local certificate.
The external call overhead remains separate and explicitly charged. -/
theorem LocalBound.atomic {I : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
    (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)
    {A B : Type} {a : C.Str A} {b : C.Str B} {f : A → B} {code : Q.Realizer a b f}
    (bound : LocalBound code) (pre : A → Prop) (post : B → Prop) (localTime callTime : Nat)
    (ht : ∀ input, pre input → bound.time input ≤ localTime)
    (hp : ∀ input, pre input → post (f input))
    (hc : ∀ input, pre input → control.localCall (Q.size a input) (Q.size b (f input)) ≤ callTime) :
    Bounds control queryCost (Code.atomic (iface := iface) code) pre post (localTime + callTime) := by
  apply Bounds.atomic
  intro input hi
  exact ⟨hp input hi, Nat.add_le_add ((bound.cost_le input).trans (ht input hi)) (hc input hi)⟩

namespace Language

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {S : Type} {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)

def contextReturnBound {B E : Type} (b : C.Str B) (e : C.Str E) (store : C.Str S) :
    LocalBound (contextReturn (Q := Q) b e store) :=
  LocalBound.pair laws
    (LocalBound.pair laws (LocalBound.compose laws (LocalBound.fst laws _ _) (LocalBound.fst laws _ _))
      (LocalBound.snd laws _ _))
    (LocalBound.compose laws (LocalBound.fst laws _ _) (LocalBound.snd laws _ _))

def contextInputBound {A E : Type} (a : C.Str A) (e : C.Str E) (store : C.Str S)
    {f : A → E} {context : Q.Realizer a e f} (bound : LocalBound context) :
    LocalBound (contextInput a e store context) :=
  LocalBound.pair laws (LocalBound.identity laws _)
    (LocalBound.compose laws (LocalBound.fst laws _ _) bound)

variable {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  (P : Primitives base Op)
  (primitive : {a b : Ty Atom} → (instr : Op a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty Atom} → (instr : Op a b) → LocalBound (primitive instr))
  (store : C.Str S)

def chooseBound {Γ} (cond : Expr Op Γ .bool) :
    LocalBound (choose rep data P primitive store cond) :=
  LocalBound.compose laws
    (LocalBound.pair laws
      (LocalBound.compose laws (LocalBound.fst laws _ _)
        (Expression.compileBound rep data P primitive laws dataLaws primitiveBound cond))
      (LocalBound.identity laws _)) (dataLaws.selectBound _)

def loopInputBound {Γ a} (count : Expr Op Γ .nat) (init : Expr Op Γ a) :
    LocalBound (loopInput rep data P primitive store count init) :=
  LocalBound.pair laws
    (LocalBound.compose laws (LocalBound.fst laws _ _)
      (Expression.compileBound rep data P primitive laws dataLaws primitiveBound count))
    (LocalBound.pair laws
      (LocalBound.pair laws
        (LocalBound.compose laws (LocalBound.fst laws _ _)
          (Expression.compileBound rep data P primitive laws dataLaws primitiveBound init))
        (LocalBound.fst laws _ _)) (LocalBound.snd laws _ _))

def loopOutputBound {Γ a} : LocalBound (loopOutput (Q := Q) rep store (Γ := Γ) (a := a)) :=
  LocalBound.pair laws (LocalBound.compose laws (LocalBound.fst laws _ _) (LocalBound.fst laws _ _))
    (LocalBound.snd laws _ _)

end Language

end Signatures.Runtime.BackendProgram
