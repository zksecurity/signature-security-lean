import Signatures.Runtime.ProgramRange
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp Signatures.Runtime NaturalRange

namespace SignaturesTest.ProgramRange

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private abbrev Base := cryptoBase (ZMod 3) (ZMod 3) (ZMod 3) Unit Unit
private def P := arithmetic (ZMod 3) (ZMod 3) (ZMod 3) Unit Unit PrimitiveCosts.unit
private def sampling : Machine.SamplingCosts := ⟨2, fun n => n + 1⟩

private theorem sampling_width (n : Nat) : n < 2^(sampling.uniform n) :=
  n.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [sampling]; omega))

private def double : Program CryptoOp (Machine.Effect .nat) [.nat] .nat :=
  .ret (.op .natAdd (.pair (.var .here) (.var .here)))

-- An oracle response is written/read through the store, then controls the
-- number of calls. This is not a fixed query-independent execution path.
private def adaptive : Machine.Code [] .nat where
  store := .nat
  init := .nat 0
  body := .bind (.query (.uniform 3) .unit)
    (.bind (.query .write (.op (.finVal 3) (.var .here)))
      (.bind (.query .read .unit)
        (.loop (.var .here) (.nat 1)
          (.call double (.cons (.var .here) .nil)))))

private def fixedReply (draw : Nat) :
    HandlerM Base (Machine.Effect .nat) (StateT Nat Id) := fun cmd arg state =>
  match cmd with
  | .scalar => pure (⟨0, sampling.scalar⟩, state)
  | .uniform n => pure (⟨⟨draw % (n+1), Nat.mod_lt _ (by omega)⟩, sampling.uniform n⟩, state)
  | .read => pure (⟨state, 1⟩, state)
  | .write => pure (⟨(), 1⟩, arg)

#eval show IO Unit from do
  for n in [0, 1, 2, 3] do
    let init := adaptive.init.run P ()
    let out := (adaptive.body.run P (fixedReply n) ()).run init.value
    unless out.1.value == 2^n && out.2 == n do
      throw <| IO.userError "adaptive store/call/loop execution mismatch"
    unless out.1.value < 2^(init.steps + out.1.steps + 2) do
      throw <| IO.userError "machine natural bound failed"

example [SampleableType (ZMod 3)] (z : Run Nat)
    (hz : z ∈ support (adaptive.run (F := ZMod 3) (G₁ := ZMod 3) (G₂ := ZMod 3)
      (K := Unit) (M := Unit) PrimitiveCosts.unit sampling ())) : z.value < 2^z.steps := by
  simpa only [Nat.zero_add, ValueBound] using machine_bound PrimitiveCosts.unit sampling sampling_width
    adaptive 0 () (by trivial) z hz

-- A zero-cost arbitrary-width uniform sampler does not meet the implementation
-- obligation. Merely having a finite output type is insufficient.
example : ¬ ∀ n : Nat, n < 2^(0 : Nat) := by
  intro h
  have := h 1
  norm_num at this

end SignaturesTest.ProgramRange

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``args_bound, ``args_trace_bound, ``program_bound,
      ``effects_bound, ``machine_bound] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
