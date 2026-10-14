import Signatures.Model.Hardness

/-! The maximum advantage allowed by a specified implementation/resource
class. This is a supremum, so it does not presume an optimal solver exists.
A numerical hardness assumption can separately upper-bound this quantity. -/

namespace Model

noncomputable def advantageBound {Solver : Type*} (advantage : Solver → ENNReal)
    (within : Solver → Prop) : ENNReal :=
  ⨆ solver, ⨆ (_ : within solver), advantage solver

theorem le_advantageBound {Solver : Type*} (advantage : Solver → ENNReal)
    (within : Solver → Prop) (solver : Solver) (h : within solver) :
    advantage solver ≤ advantageBound advantage within :=
  le_iSup_of_le solver (le_iSup_of_le h le_rfl)

theorem hardWithin_advantageBound {Solver : Type*} (advantage : Solver → ENNReal)
    (within : Nat → Solver → Prop) (budget : Nat) :
    HardWithin advantage within budget (advantageBound advantage (within budget)) :=
  fun solver h => le_advantageBound advantage (within budget) solver h

theorem advantageBound_le {Solver : Type*} (advantage : Solver → ENNReal)
    (within : Nat → Solver → Prop) (budget : Nat) (epsilon : ENNReal)
    (hardness : HardWithin advantage within budget epsilon) :
    advantageBound advantage (within budget) ≤ epsilon :=
  iSup_le fun solver => iSup_le fun h => hardness solver h

end Model
