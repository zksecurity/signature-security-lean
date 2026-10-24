import Proofs.Runtime.HeapMachineCode

/-! Increasing a heap envelope only increases the syntax-computed cost bound.
This lets a package use one envelope for loading and execution. -/

namespace Signatures.Runtime

namespace HeapExpression

theorem budget_mono (w : Nat) {n m : Nat} (h : n ≤ m)
    {Γ a} (e : Expr CryptoOp Γ a) : budget w n e ≤ budget w m e := by
  induction e <;>
    simp only [budget, primitiveBudget, readBudget, allocBudget, frameBudget, tapeBudget] <;>
    gcongr

end HeapExpression

namespace HeapArguments

theorem budget_mono (w : Nat) {n m : Nat} (h : n ≤ m)
    {Γ Δ} (args : Args CryptoOp Γ Δ) : budget w n args ≤ budget w m args := by
  induction args with
  | nil => rfl
  | cons head tail ih =>
    simp only [budget, HeapExpression.frameBudget]
    have := HeapExpression.budget_mono w h head
    gcongr

end HeapArguments

namespace HeapProgram

theorem budget_mono {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}
    (w : Nat) {n m : Nat} (h : n ≤ m)
    (f g : {a b : Ty CryptoAtom} → Cmd a b → Nat) (hfg : ∀ {a b} (cmd : Cmd a b), f cmd ≤ g cmd)
    {Γ a} (code : Program CryptoOp Cmd Γ a) : budget w n f code ≤ budget w m g code := by
  induction code with
  | ret e =>
    exact max_le_max (HeapExpression.budget_mono w h e) (le_refl _)
  | query cmd e =>
    exact max_le_max (HeapExpression.budget_mono w h e) (Nat.add_le_add_right (hfg cmd) 1)
  | bind first body ih₁ ih₂ =>
    simp only [budget, HeapExpression.frameBudget]
    gcongr
  | branch cond yes no ih₁ ih₂ =>
    simp only [budget, HeapExpression.readBudget, HeapExpression.tapeBudget]
    have := HeapExpression.budget_mono w h cond
    gcongr
  | loop count init body ih =>
    simp only [budget, HeapExpression.readBudget, HeapExpression.tapeBudget, HeapExpression.frameBudget]
    have := HeapExpression.budget_mono w h count
    have := HeapExpression.budget_mono w h init
    gcongr
  | call body args ih =>
    simp only [budget]
    have := HeapArguments.budget_mono w h args
    gcongr

end HeapProgram

namespace HeapMachine

theorem fee_mono (w r k : Nat) {n m : Nat} (h : n ≤ m)
    {storage a b} (cmd : Machine.Effect storage a b) : fee w r k n cmd ≤ fee w r k m cmd := by
  cases cmd <;> simp only [fee, HeapExpression.allocBudget, HeapExpression.tapeBudget] <;> gcongr

theorem budget_mono (w r k : Nat) {n m : Nat} (h : n ≤ m)
    {Γ a} (code : Machine.Code Γ a) : budget w r k n code ≤ budget w r k m code :=
  max_le_max (le_refl _) (max_le_max (HeapExpression.budget_mono w h code.init)
    (HeapProgram.budget_mono w h (fee w r k n) (fee w r k m) (fee_mono w r k h) code.body))

end HeapMachine

end Signatures.Runtime
