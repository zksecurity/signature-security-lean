import Signatures.Runtime.Caliper.ExpressionCompilation
import Signatures.Runtime.Caliper.BranchBudgets
import Signatures.Runtime.Caliper.FixedFoldBudgets
import Signatures.Runtime.Caliper.StagedFoldBounds

/-! Structural time/code budgets for original source expressions. Only primitive
instructions and executed final-layout conversions require supplied budgets.
Finite maxima range over traversal stages, never over the message domain. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource

structure Budget where
  time : Nat
  words : Nat

namespace Budget

def identity : Budget := ⟨0, 1⟩
def literal : Budget := ⟨7, 35⟩
def storage (width : Nat) : Budget := ⟨8 * width, 26 * width + 14⟩
def cons (width : Nat) : Budget := ⟨8 * width + 5, 26 * width + 38⟩
def seq (first second : Budget) : Budget := ⟨first.time + second.time, first.words + second.words + 1⟩
def pair (input left right : Nat) (first second : Budget) : Budget :=
  ⟨first.time + second.time + 52 * input + 36 * left + 16 * right,
   first.words + second.words + 169 * input + 117 * left + 52 * right + 124⟩
def branch (input : Nat) (test yes no : Budget) : Budget :=
  ⟨test.time + yes.time + no.time + 76 * input + 43,
   test.words + yes.words + no.words + 273 * input + 304⟩
def foldFrame (input list state : Nat) (values initial : Budget) : Budget :=
  pair input list (state + input) values (pair input state input initial identity)
def fixedFold (entry state env capacity : Nat) (body : Budget) : Budget :=
  ⟨8 * state + capacity * (body.time + 44 * ListFold.width entry state env capacity + 7),
   26 * state + 14 + capacity * (body.words + 169 * ListFold.width entry state env capacity + 115)⟩
def stagedFold (layoutWords capacity : Nat) (body stop : Budget) : Budget :=
  ⟨StagedFold.timeBudget layoutWords body.time stop.time capacity,
   StagedFold.codeBudget layoutWords body.words stop.words capacity⟩

def maximum {n : Nat} (family : Fin n → Budget) : Budget :=
  ⟨Finset.univ.sup (fun i => (family i).time), Finset.univ.sup (fun i => (family i).words)⟩
theorem time_le_maximum {n : Nat} (family : Fin n → Budget) (i : Fin n) :
    (family i).time ≤ (maximum family).time := Finset.le_sup (f := fun i => (family i).time) (Finset.mem_univ i)
theorem words_le_maximum {n : Nat} (family : Fin n → Budget) (i : Fin n) :
    (family i).words ≤ (maximum family).words := Finset.le_sup (f := fun i => (family i).words) (Finset.mem_univ i)

def layoutBound {n : Nat} (entry env : Nat) (states : Fin n → Nat) : Nat :=
  max entry (max env (Finset.univ.sup states))

end Budget

structure Implementation.Budget {w : Nat} {A B : Type} {input : Layout w A} {output : Layout w B}
    {f : A → B} (implementation : Implementation Caliper.CostModel.unit input output f) where
  estimate : BoundedSource.Budget
  bounded : implementation.BoundedBy estimate.time estimate.words

end Signatures.Runtime.CaliperBackend.BoundedSource

namespace Signatures.Runtime.CaliperBackend.SourceExpression

open Caliper BoundedSource

variable {w : Nat} {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
    {P : Primitives base Op} {hw : 16 < 2 ^ w}

def Variable.budget {Γ : List (Ty Atom)} {a : Ty Atom} {v : Var Γ a}
    {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)} :
    Variable v input output → Budget
  | .here head _ _ => .storage head.representation.encoding.words
  | .there (tail := tail) _ rest _ => (Budget.storage tail.representation.encoding.words).seq rest.budget

theorem Variable.bounded {Γ : List (Ty Atom)} {a : Ty Atom} {v : Var Γ a}
    {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    (access : Variable v input output) (hw : 16 < 2 ^ w) :
    (access.compile (cost := .unit) (by decide) hw).BoundedBy access.budget.time access.budget.words := by
  induction access with
  | here head tail fits => exact Implementation.first_boundedBy head tail hw fits
  | there head rest fits ih => exact (Implementation.second_boundedBy head _ hw fits).then ih

def Compilation.LocalBounds {Γ : List (Ty Atom)} {a : Ty Atom}
    {expression : Expr Op Γ a} {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)} :
    Compilation P .unit hw expression input output → Type
  | .var _ | .unit _ | .bool _ _ | .nat _ _ _ _ _ | .nil _ _ _ _ _ => Unit
  | .pair first second _ _ _ => first.LocalBounds × second.LocalBounds
  | .fst _ _ _ code | .snd _ _ _ code => code.LocalBounds
  | .cons _ _ _ _ head tail _ _ => head.LocalBounds × tail.LocalBounds
  | .branch test yes no _ _ => test.LocalBounds × yes.LocalBounds × no.LocalBounds
  | .letE _ _ _ binding code => binding.LocalBounds × code.LocalBounds
  | .op _ implementation code => code.LocalBounds × implementation.Budget
  | .fold _ _ _ _ _ _ _ values initial body => values.LocalBounds × initial.LocalBounds × body.LocalBounds
  | .foldStages _ _ _ _ _ _ _ _ values initial bodies stops =>
      values.LocalBounds × initial.LocalBounds × (∀ i, (bodies i).LocalBounds) × (∀ i, (stops i).Budget)
  | .view code _ _ | .listWiden _ _ _ _ _ _ code => code.LocalBounds

def Compilation.budget {Γ : List (Ty Atom)} {a : Ty Atom}
    {expression : Expr Op Γ a} {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    (code : Compilation P .unit hw expression input output) : code.LocalBounds → Budget :=
  match code with
  | .var access => fun _ => access.budget
  | .unit _ => fun _ => .storage 0
  | .bool _ _ | .nat _ _ _ _ _ => fun _ => .literal
  | .pair (left := left) (right := right) first second _ _ _ => fun bounds =>
      .pair input.representation.encoding.words left.representation.encoding.words right.representation.encoding.words
        (first.budget bounds.1) (second.budget bounds.2)
  | .fst left _ _ code => fun bounds => (code.budget bounds).seq (.storage left.representation.encoding.words)
  | .snd _ right _ code => fun bounds => (code.budget bounds).seq (.storage right.representation.encoding.words)
  | .nil _ entry capacity _ _ => fun _ => .storage (1 + capacity * entry.representation.encoding.words)
  | .cons entry capacity _ _ head tail _ _ => fun bounds =>
      (Budget.pair input.representation.encoding.words entry.representation.encoding.words (1 + capacity * entry.representation.encoding.words)
        (head.budget bounds.1) (tail.budget bounds.2)).seq (.cons (1 + (capacity + 1) * entry.representation.encoding.words))
  | .branch test yes no _ _ => fun bounds => .branch input.representation.encoding.words
      (test.budget bounds.1) (yes.budget bounds.2.1) (no.budget bounds.2.2)
  | .letE localValue _ _ binding code => fun bounds =>
      (Budget.pair input.representation.encoding.words localValue.representation.encoding.words input.representation.encoding.words
        (binding.budget bounds.1) .identity).seq (code.budget bounds.2)
  | .op _ _ code => fun bounds => (code.budget bounds.1).seq bounds.2.estimate
  | .fold input entry state capacity _ _ _ values initial body => fun bounds =>
      (Budget.foldFrame input.representation.encoding.words (1 + capacity * entry.representation.encoding.words) state.representation.encoding.words
        (values.budget bounds.1) (initial.budget bounds.2.1)).seq
        (.fixedFold entry.representation.encoding.words state.representation.encoding.words input.representation.encoding.words capacity
          (body.budget bounds.2.2))
  | .foldStages input entry _ capacity states _ _ _ values initial bodies _ => fun bounds =>
      (Budget.foldFrame input.representation.encoding.words (1 + capacity * entry.representation.encoding.words) (states 0).representation.encoding.words
        (values.budget bounds.1) (initial.budget bounds.2.1)).seq
        (.stagedFold (Budget.layoutBound entry.representation.encoding.words input.representation.encoding.words
          (fun i => (states i).representation.encoding.words)) capacity
          (.maximum (fun i => (bodies i).budget (bounds.2.2.1 i))) (.maximum (fun i => (bounds.2.2.2 i).estimate)))
  | .view code _ _ => fun bounds => (code.budget bounds).seq .identity
  | .listWiden entry _ target _ _ _ code => fun bounds =>
      (code.budget bounds).seq (.storage (1 + target * entry.representation.encoding.words))

end Signatures.Runtime.CaliperBackend.SourceExpression
