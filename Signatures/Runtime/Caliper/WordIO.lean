import Signatures.Runtime.Caliper.BoundedSource

/-! A word I/O boundary for Caliper programs. Local computation is still literal
Caliper code. The added effects receive one external word into a register,
send one register word, or invoke the external oracle, at explicit costs. None allocates memory or
evaluates an arbitrary host function. Oracle protocol semantics are separate.

The trace records external I/O, not the private random tape. Reply storage must
be allocated and filled using ordinary Caliper instructions.
-/

namespace Signatures.Runtime.CaliperBackend.WordIO

open Caliper

variable {w : Nat}

structure Costs where
  machine : CostModel
  read : Nat
  write : Nat
  invoke : Nat

def Costs.unit : Costs := ⟨.unit, 1, 1, 1⟩

inductive Event (w : Nat) where
  | input (value : Word w)
  | output (value : Word w)
  | invoke
deriving DecidableEq, Repr

inductive Code (w : Nat) where
  | compute (code : Stmt w)
  | read (destination : Reg)
  | write (source : Reg)
  | invoke
  | seq (first second : Code w)
  | branch (condition : Reg) (yes no : Code w)

inductive Exec (cost : Costs) (tape : RandomTape w) :
    Code w → State w → State w → List (Event w) → Nat → Int → Int → Prop where
  | compute {code before after time net peak} :
      Caliper.Exec cost.machine tape code before after time net peak →
      Exec cost tape (.compute code) before after [] time net peak
  | read {destination value before} :
      Exec cost tape (.read destination) before (before.setReg destination value)
        [.input value] cost.read 0 0
  | write {source before} :
      Exec cost tape (.write source) before before [.output (before.regs source)] cost.write 0 0
  | invoke {before} : Exec cost tape .invoke before before [.invoke] cost.invoke 0 0
  | seq {first second before middle after left right t₁ t₂ d₁ d₂ p₁ p₂} :
      Exec cost tape first before middle left t₁ d₁ p₁ →
      Exec cost tape second middle after right t₂ d₂ p₂ →
      Exec cost tape (.seq first second) before after (left ++ right)
        (t₁ + t₂) (d₁ + d₂) (max p₁ (d₁ + p₂))
  | branch_yes {condition yes no before after trace time net peak} :
      before.regs condition ≠ 0 → Exec cost tape yes before after trace time net peak →
      Exec cost tape (.branch condition yes no) before after trace (cost.machine.branch + time) net peak
  | branch_no {condition yes no before after trace time net peak} :
      before.regs condition = 0 → Exec cost tape no before after trace time net peak →
      Exec cost tape (.branch condition yes no) before after trace (cost.machine.branch + time) net peak

def Code.Writes : Code w → Reg → Prop
  | .compute code, register => code.Writes register
  | .read destination, register => register = destination
  | .write _, _ | .invoke, _ => False
  | .seq first second, register => first.Writes register ∨ second.Writes register
  | .branch _ yes no, register => yes.Writes register ∨ no.Writes register

def Code.Touches : Code w → BufId → Prop
  | .compute code, buffer => code.Touches buffer
  | .read _, _ | .write _, _ | .invoke, _ => False
  | .seq first second, buffer => first.Touches buffer ∨ second.Touches buffer
  | .branch _ yes no, buffer => yes.Touches buffer ∨ no.Touches buffer

def Code.RandomFree : Code w → Prop
  | .compute code => code.RandomFree
  | .read _ | .write _ | .invoke => True
  | .seq first second => first.RandomFree ∧ second.RandomFree
  | .branch _ yes no => yes.RandomFree ∧ no.RandomFree

/-- The I/O envelope has its own finite prefix encoding. The embedded local
program is charged in full, including its instruction tags and operands. -/
def Code.description : Code w → List Nat
  | .compute code => 0 :: CaliperBackend.description code
  | .read destination => [1, destination]
  | .write source => [2, source]
  | .invoke => [5]
  | .seq first second => 3 :: (first.description ++ second.description)
  | .branch condition yes no => 4 :: condition :: (yes.description ++ no.description)

def Code.DescriptionFits (code : Code w) : Prop := ∀ token ∈ code.description, token < 2 ^ w
def Code.descriptionWords (code : Code w) : Nat := code.description.length

theorem Exec.frame_reg {cost : Costs} {tape : RandomTape w} {code : Code w}
    {before after : State w} {trace : List (Event w)} {time : Nat} {net peak : Int}
    (execution : Exec cost tape code before after trace time net peak)
    {register : Reg} (untouched : ¬ code.Writes register) : after.regs register = before.regs register := by
  induction execution with
  | compute execution => exact execution.frame_reg untouched
  | read => exact regs_setReg_ne _ _ untouched
  | write | invoke => rfl
  | seq _ _ ih₁ ih₂ =>
    rw [ih₂ (fun h => untouched (Or.inr h)), ih₁ (fun h => untouched (Or.inl h))]
  | branch_yes _ _ ih => exact ih (fun h => untouched (Or.inl h))
  | branch_no _ _ ih => exact ih (fun h => untouched (Or.inr h))

theorem Exec.frame_buf {cost : Costs} {tape : RandomTape w} {code : Code w}
    {before after : State w} {trace : List (Event w)} {time : Nat} {net peak : Int}
    (execution : Exec cost tape code before after trace time net peak)
    {buffer : BufId} (untouched : ¬ code.Touches buffer) :
    after.bufs buffer = before.bufs buffer ∧ after.caps buffer = before.caps buffer := by
  induction execution with
  | compute execution => exact ⟨execution.frame_buf untouched, execution.frame_cap untouched⟩
  | read | write | invoke => exact ⟨rfl, rfl⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨h₁, c₁⟩ := ih₁ (fun h => untouched (Or.inl h))
    obtain ⟨h₂, c₂⟩ := ih₂ (fun h => untouched (Or.inr h))
    exact ⟨h₂.trans h₁, c₂.trans c₁⟩
  | branch_yes _ _ ih => exact ih (fun h => untouched (Or.inl h))
  | branch_no _ _ ih => exact ih (fun h => untouched (Or.inr h))

theorem Exec.wellFormed_preserved {cost : Costs} {tape : RandomTape w} {code : Code w}
    {before after : State w} {trace : List (Event w)} {time : Nat} {net peak : Int}
    (execution : Exec cost tape code before after trace time net peak)
    (wellFormed : before.WellFormed) : after.WellFormed := by
  induction execution with
  | compute execution => exact execution.wellFormed_preserved wellFormed
  | read => exact ⟨wellFormed.size_le_cap, wellFormed.finite⟩
  | write | invoke => exact wellFormed
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ wellFormed)
  | branch_yes _ _ ih | branch_no _ _ ih => exact ih wellFormed

theorem Exec.tapePos_eq {cost : Costs} {tape : RandomTape w} {code : Code w}
    {before after : State w} {trace : List (Event w)} {time : Nat} {net peak : Int}
    (execution : Exec cost tape code before after trace time net peak)
    (randomFree : code.RandomFree) : after.tapePos = before.tapePos := by
  induction execution with
  | compute execution => exact execution.tapePos_eq_of_randomFree randomFree
  | read | write | invoke => rfl
  | seq _ _ ih₁ ih₂ => exact (ih₂ randomFree.2).trans (ih₁ randomFree.1)
  | branch_yes _ _ ih => exact ih randomFree.1
  | branch_no _ _ ih => exact ih randomFree.2

end Signatures.Runtime.CaliperBackend.WordIO
