import Signatures.Runtime.SchnorrRawFork
import Signatures.Runtime.SchnorrRawTapeBounds
import Signatures.Runtime.BackendSchnorrRawUniformPolynomial
import Signatures.Runtime.BackendSchnorrRawChallengeBudget
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Raw replay must preserve every private draw in its original family order.
The native private draw takes a dynamic arity and uses stored naturals directly
on valid hits. Both raw draw families have checked capacity/encoding and native
costs; the full controller/general-caller certificate remains separate. -/

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

/-- Query counts do not enumerate a range, even when its arity is chosen
adaptively and is exponentially larger than its binary description. -/
private def adaptivePass : OracleComp Spec Nat := do
  let bit ← Spec.query (.inl 1)
  let value ← Spec.query (.inl (if bit.val = 0 then 2 ^ 64 else 1))
  pure value.val

private theorem adaptiveQueries : IsTotalQueryBound adaptivePass 2 := by
  simp [adaptivePass, IsTotalQueryBound]

example (out : Nat × RawTape.State (Fin 2))
    (supported : out ∈ support ((simulateQ RawTape.oracle adaptivePass).run {})) :
    out.2.saved.length ≤ 2 ∧ out.2.remaining = [] :=
  RawTape.firstPass_growth adaptivePass 2 adaptiveQueries out supported

example (first second : Nat × RawTape.State (Fin 2))
    (firstSupported : first ∈ support ((simulateQ RawTape.oracle adaptivePass).run {}))
    (secondSupported : second ∈ support
      ((simulateQ RawTape.oracle adaptivePass).run (RawTape.restart 0 1 first.2))) :
    second.2.saved.length ≤ 5 ∧ second.2.remaining.length ≤ 3 :=
  RawTape.replay_growth adaptivePass (fun _ => adaptivePass) 2 2 adaptiveQueries
    (fun _ => adaptiveQueries) first firstSupported 0 1 second secondSupported

example (state : RawTape.State (Fin 2)) :
    IsTotalQueryBound ((simulateQ RawTape.oracle adaptivePass).run state) 2 :=
  RawTape.simulate_queryBound adaptivePass 2 adaptiveQueries state

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

/-- The scan cost proof covers the existing code with any retained context. -/
example (Γ : List (Ty CryptoAtom)) :
    SeedTape.popCode.weakenTail Γ = SeedTape.NativeScan.scan (Γ := Γ) :=
  SeedTape.NativeScan.scan_eq Γ

private def challengeState : RawTape.State F :=
  ⟨[(3, 0, 1), (1, 2, 0), (3, 0, 0), (1, 4, 0)],
    [(3, 0, 1), (1, 2, 0), (3, 0, 0), (1, 4, 0)]⟩

/-- A challenge hit consumes the first challenge without reordering private
draws or changing the saved transcript. The later challenge stays available. -/
example : NativeChallenge.prepareExpression.denote
    (arithmetic F F F Nat Nat PrimitiveCosts.unit)
    (NativeUniform.encodeState challengeState, ()) =
      (true, (2, (challengeState.saved, [(3, 0, 1), (3, 0, 0), (1, 4, 0)]))) := by
  rw [NativeChallenge.prepareExpression_value]
  rfl

example : NativeChallenge.prepareExpression.denote
    (arithmetic F F F Nat Nat PrimitiveCosts.unit) (([(3, 0, 1)], [(3, 0, 1)]), ()) =
      (false, (0, ([(3, 0, 1)], [(3, 0, 1)]))) := by
  rw [NativeChallenge.prepareExpression_value]
  rfl

example : NativeChallenge.saveExpression.denote
    (arithmetic F F F Nat Nat PrimitiveCosts.unit) ((4, ([(3, 0, 1)], [(3, 0, 1)])), ()) =
      (4, ([(3, 0, 1), (1, 4, 0)], [(3, 0, 1)])) := by
  rw [NativeChallenge.saveExpression_value]
  rfl

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawTape.oracle_seeded, ``RawTape.run'_seeded, ``RawTape.run_log,
      ``RawTape.toSeed_encode, ``RawTape.restart_seed, ``RawTape.fork_eq_lazy,
      ``RawTape.dlogReduction_eq_lazy, ``RawTape.security, ``RawTape.encode_valid,
      ``RawTape.pop_valid, ``RawTape.decode_uniform_val, ``RawTape.oracle_valid,
      ``RawTape.simulate_valid, ``RawTape.restart_valid,
      ``RawTape.oracle_growth, ``RawTape.oracle_saved_extends, ``RawTape.simulate_growth,
      ``RawTape.simulate_queryBound, ``RawTape.firstPass_growth, ``RawTape.restart_length,
      ``RawTape.replay_growth, ``SeedTape.pop_sublist, ``SeedTape.pop_answer_mem_or_default,
      ``SeedTape.pop_answer_mem, ``SeedTape.trim_sublist,
      ``NativeUniform.prepareExpression_value, ``NativeUniform.saveExpression_value,
      ``NativeUniform.denote, ``NativeUniform.source, ``NativeUniform.description,
      ``NativeUniform.pop_property, ``NativeUniform.prepare_property,
      ``NativeUniform.hit_property, ``NativeUniform.save_property, ``NativeUniform.restart_property,
      ``NativeUniform.cell_size, ``NativeUniform.tape_size, ``NativeUniform.state_size,
      ``NativeUniform.input_size, ``NativeUniform.draw_size, ``NativeUniform.prepare_size,
      ``NativeUniform.code_property, ``NativeUniform.hit_cost, ``NativeUniform.save_cost,
      ``SeedTape.NativeScan.scan_eq, ``SeedTape.NativeScan.step_invariant,
      ``SeedTape.NativeScan.fold_invariant, ``SeedTape.NativeScan.body_time,
      ``SeedTape.NativeScan.forward_time, ``SeedTape.NativeScan.scan_time, ``SeedTape.NativeScan.scan_cost,
      ``NativeUniform.prepare_cost, ``NativeUniform.bound, ``NativeUniform.runtimeBound_polynomial,
      ``NativeChallenge.prepareExpression_value, ``NativeChallenge.saveExpression_value,
      ``NativeChallenge.denote, ``NativeChallenge.source, ``NativeChallenge.description,
      ``NativeChallenge.prepare_property, ``NativeChallenge.save_property,
      ``NativeChallenge.output_size, ``NativeChallenge.prepare_size,
      ``NativeChallenge.prepare_cost, ``NativeChallenge.save_cost, ``NativeChallenge.bound,
      ``NativeChallenge.runtimeBound_polynomial] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``RawTape.fork_eq_lazy, ``RawTape.dlogReduction_eq_lazy, ``NativeChallenge.source] do
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
  for name in #[``NativeUniform.code, ``NativeUniform.descriptionBound,
      ``NativeChallenge.code, ``NativeChallenge.descriptionBound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        if (← inferType param).isConstOf ``Nat then
          unless (← getFVarLocalDecl param).userName == `allowance do
            throwError "{name}: code and its static bound must not depend on input arity or tape length"
  for name in #[``NativeUniform.hit_cost, ``NativeUniform.save_cost, ``NativeUniform.prepare_cost,
      ``NativeUniform.bound, ``SeedTape.NativeScan.scan_cost] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``NativeUniform.hit, ``NativeUniform.save, ``NativeUniform.prepare,
            ``NativeUniform.code, ``SeedTape.popCode, ``BackendProgram.Bounds,
            ``BackendProgram.Expression.compile, ``BackendProgram.Expression.compileBound] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: completed adapter/compiled-expression costs must be derived"
  for name in #[``NativeUniform.saveTime, ``NativeUniform.prepareTime, ``NativeUniform.runtimeBound,
      ``NativeChallenge.prepareTime, ``NativeChallenge.saveTime, ``NativeChallenge.runtimeBound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        if (← inferType param).isConstOf ``Nat then
          unless #[`width, `savedCap, `remainingCap, `comparisonTime, `zeroTime, `addTime,
              `requestTime, `responseTime, `queryTime, `sampleTime].contains (← getFVarLocalDecl param).userName do
            throwError "{name}: runtime must depend on encoded width, tape capacities and primitive costs, not numeric arity"
  for name in #[``NativeUniform.bound, ``NativeChallenge.bound] do
    forallTelescope (← getConstInfo name).type fun _ conclusion => do
      unless conclusion.isAppOf ``BackendProgram.Bounds do
        throwError "{name}: runtime must bound the entire native program on all supported runs"
  for name in #[``NativeChallenge.prepare_cost, ``NativeChallenge.save_cost, ``NativeChallenge.bound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``NativeChallenge.prepare, ``NativeChallenge.save, ``NativeChallenge.code,
            ``SeedTape.popCode, ``BackendProgram.Expression.compile, ``BackendProgram.Expression.compileBound] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: challenge handler/component costs must be derived"
  forallTelescope (← getConstInfo ``NativeChallenge.bound).type fun params _ => do
    let some sampler ← params.findM? (fun param => return (← getFVarLocalDecl param).userName == `sampler)
      | throwError "challenge handler must take actual scalar-sampling code"
    for param in params do
      let type ← inferType param
      if type.isAppOf ``BackendProgram.Bounds then
        unless type.getAppArgs.contains sampler do
          throwError "challenge handler may assume only the scalar sampler's component budget"

end SignaturesTest.SchnorrRawTape
