import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-! A shared lazy random oracle, with named requests and query helpers.
`run` starts one empty oracle shared by the attacker, signer, and verifier. -/

open OracleComp OracleSpec

namespace Model.RandomOracle

abbrev Spec (Input Output : Type) := unifSpec + (Input →ₒ Output)
abbrev Computation (Input Output : Type) := OracleComp (Spec Input Output)
abbrev Request (Input : Type) := (Spec Input Unit).Domain

namespace Request

@[match_pattern] abbrev random {Input : Type} (n : Nat) : Request Input := .inl n
@[match_pattern] abbrev hash {Input : Type} (input : Input) : Request Input := .inr input

end Request

abbrev random {Input Output : Type} (n : Nat) : Computation Input Output (Fin (n + 1)) :=
  liftM ((Spec Input Output).query (Request.random n))

abbrev hash {Input Output : Type} (input : Input) : Computation Input Output Output :=
  liftM ((Spec Input Output).query (Request.hash input))

abbrev sample {Input Output : Type} (Value : Type) [SampleableType Value] :
    Computation Input Output Value := liftM ($ᵗ Value)

/-- Execute all hash queries against the same initially empty lazy oracle. -/
noncomputable def run {Input Output α : Type} [DecidableEq Input] [SampleableType Output]
    (program : Computation Input Output α) : ProbComp α :=
  (simulateQ (Input →ₒ Output).romImpl program).run' ∅

end Model.RandomOracle
