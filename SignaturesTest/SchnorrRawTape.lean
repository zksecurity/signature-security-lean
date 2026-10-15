import Signatures.Runtime.SchnorrRawFork
import Signatures.Runtime.BackendSchnorrRawUniform
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Raw replay must preserve every private draw in its original family order.
The native private draw takes a dynamic arity and uses stored naturals directly
on valid hits. No native runtime bound is asserted by these tests. -/

open OracleComp OracleSpec Signatures.Runtime
open Signatures.Runtime.Schnorr Signatures.Runtime.Schnorr.RawTape

namespace SignaturesTest.SchnorrRawTape

private abbrev Spec := RawTape.Spec (Fin 2)

private def pass : OracleComp Spec (Fin 2 × Fin 2 × Fin 2) := do
  let challenge ← Spec.query (.inr ())
  let caller ← Spec.query (.inl 1)
  let simulator ← Spec.query (.inl 1)
  pure (challenge, caller, simulator)

private def recorded : RawTape.State (Fin 2) :=
  ⟨[(1, 0, 0), (3, 0, 1), (3, 0, 0)], []⟩

/-- Both post-challenge private values stay in their original order. -/
example : (simulateQ RawTape.oracle pass).run' (RawTape.restart 0 1 recorded) =
    pure (1, 1, 0) := rfl

example : RawTape.Valid (RawTape.restart 0 1 recorded).remaining := by
  apply (RawTape.restart_valid 0 1 recorded ?_).2
  simp [RawTape.Valid, RawTape.ValidCell, recorded]

example : RawTape.fork pass 0 (fun _ => some (0 : Fin 1)) =
    _root_.Schnorr.LazyROM.fork pass 0 (fun _ => some (0 : Fin 1)) :=
  RawTape.fork_eq_lazy pass 0 _

private abbrev F := ZMod 5
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A million-sized arity is handled as an input natural, with one tape cell. -/
example : NativeUniform.prepareExpression.denote
    (arithmetic F F F Nat Nat PrimitiveCosts.unit)
    ((1000000, [(1000002, 0, 999999)], [(1000002, 0, 999999)]), ()) =
      (true, (999999, (1000002, ([(1000002, 0, 999999)], [])))) := by
  rw [NativeUniform.prepareExpression_value]
  rfl

/-- On a miss the original arity, saved cells and unconsumed tape are retained. -/
example : NativeUniform.prepareExpression.denote
    (arithmetic F F F Nat Nat PrimitiveCosts.unit)
    ((1000000, [(3, 0, 1)], [(3, 0, 1)]), ()) =
      (false, (1000000, (1000002, ([(3, 0, 1)], [(3, 0, 1)])))) := by
  rw [NativeUniform.prepareExpression_value]
  rfl

example : NativeUniform.saveExpression.denote
    (arithmetic F F F Nat Nat PrimitiveCosts.unit)
    ((999999, (1000002, ([(3, 0, 1)], [(3, 0, 1)]))), ()) =
      (999999, ([(3, 0, 1), (1000002, 0, 999999)], [(3, 0, 1)])) := by
  rw [NativeUniform.saveExpression_value]
  rfl

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawTape.oracle_seeded, ``RawTape.run'_seeded, ``RawTape.run_log,
      ``RawTape.toSeed_encode, ``RawTape.restart_seed, ``RawTape.fork_eq_lazy,
      ``RawTape.dlogReduction_eq_lazy, ``RawTape.security, ``RawTape.encode_valid,
      ``RawTape.pop_valid, ``RawTape.decode_uniform_val, ``RawTape.oracle_valid,
      ``RawTape.simulate_valid, ``RawTape.restart_valid,
      ``NativeUniform.prepareExpression_value, ``NativeUniform.saveExpression_value,
      ``NativeUniform.denote, ``NativeUniform.source, ``NativeUniform.description] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``RawTape.fork_eq_lazy, ``RawTape.dlogReduction_eq_lazy] do
    forallTelescope (← getConstInfo name).type fun _ conclusion => do
      unless conclusion.isAppOf ``Eq do
        throwError "{name}: must be computation equality"
      if (conclusion.find? (fun e => e.isConstOf ``MeasureTheory.Measure)).isSome then
        throwError "{name}: must retain full computation correspondence"
  let securityType := (← getConstInfo ``RawTape.security).type
  if (securityType.find? (fun e => e.isConstOf ``instEvalDistSemanticsOfMonadLiftTSPMF)).isSome then
    throwError "raw finite-list security must use native measures"
  for forbidden in #[``OracleComp.IsPerIndexQueryBound, `Signatures.Runtime.Program,
      `Signatures.Runtime.Schnorr.SourceCertificate] do
    if (securityType.find? (fun e => e.isConstOf forbidden)).isSome then
      throwError "raw finite-list security must not restrict source syntax or require a seed cover"
  forallTelescope securityType fun params _ => do
    for param in params do
      if (← getFVarLocalDecl param).userName == `M then
        for premise in params do
          let type ← inferType premise
          if (type.isAppOf ``Finite || type.isAppOf ``Fintype || type.isAppOf ``Countable) &&
              (type.find? (fun e => e == param)).isSome then
            throwError "raw finite-list security must preserve arbitrary message types"
  for name in #[``NativeUniform.code, ``NativeUniform.descriptionBound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        if (← inferType param).isConstOf ``Nat then
          unless (← getFVarLocalDecl param).userName == `allowance do
            throwError "{name}: code and its static bound must not depend on input arity or tape length"

end SignaturesTest.SchnorrRawTape
