import Proofs.AlgebraicGroupModel.Spec.Representation
import Lean.Elab.Command

/-! Token-output utilities remain independent of oracle execution and signature games. -/

open AlgebraicGroupModel

namespace SignaturesTest.AlgebraicRepresentation

example : Representation.eval (fun b : Bool => if b then 2 else 3)
    [(true, 4), (false, 5)] = (23 : Nat) := by decide

-- A coefficient at an unavailable token contributes nothing.
example : Representation.eval (fun b : Bool => if b then 2 else 999)
    [(true, 4)] = (8 : Nat) := by decide

example : Representation.eval (fun _ : Bool => 999) ([] : Transcript Bool Nat) = 0 := rfl

-- Equal elements may have distinct input tokens and independent coefficients.
example : Representation.eval (fun b : Bool => if b then 2 else 3)
    [(true, 4), (false, 4)] = (20 : Nat) := by decide

example (out : Output Nat Bool String) (inputs : Transcript Bool Nat) :
    (out.materialize inputs).1 = out.value := rfl

open Lean Elab Command in
run_cmd do
  for name in #[`OracleComp, `AlgebraicGroupModel.Adversary,
      `Model.LazyAGM.advSpec, `Model.LazyAGM.Adversary,
      `BilinearGroup.BilinearPairing, `BLS.Statement.bls_lazy_agm_of_dlog_machine_hardness] do
    if (← getEnv).contains name then
      throwError "Representation utilities unexpectedly include oracle/adversary infrastructure: {name}"

end SignaturesTest.AlgebraicRepresentation
