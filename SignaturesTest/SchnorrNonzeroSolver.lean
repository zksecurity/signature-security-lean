import Proofs.Runtime.BackendSchnorrNonzeroSecurity
import Proofs.Runtime.BackendSchnorrNonzeroSolverPolynomial
import Proofs.Runtime.BackendSchnorrNonzeroDescriptionPolynomial
import Proofs.Runtime.BackendSchnorrNonzeroDescriptionAllowance
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Complete nonzero solver regressions: source equivalence with uncountable
messages and adaptive private randomness, original-resource certificates, both
sampling programs, and the original nonzero signing probability loss. -/

open OracleComp OracleSpec PFunctor Lean Meta
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.Schnorr

namespace SignaturesTest.SchnorrNonzeroSolver

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5
private abbrev M := Nat → Bool
private noncomputable instance : DecidableEq M := Classical.decEq M

/-- A source fixture with an adaptive million-sized private range and an
uncountable message type. It signs, then hashes the returned commitment. -/
private def adaptiveMain (_pk : F) : OracleComp (ListROM.NativeInterface.sourceSpec F F M) (M × F × F) := do
  let first ← (ListROM.NativeInterface.sourceSpec F F M).query (.inl (.inl 1000000))
  let second ← (ListROM.NativeInterface.sourceSpec F F M).query (.inl (.inl (first.val + 1)))
  let msg : M := fun n => decide (n = second.val)
  let sig ← (ListROM.NativeInterface.sourceSpec F F M).query (.inr msg)
  let challenge ← (ListROM.NativeInterface.sourceSpec F F M).query (.inl (.inr (msg, sig.1)))
  return (msg, sig.1, sig.2 + challenge)

section Source

variable {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  [Q.IsDistributive] [Q.HasOption] [OptionCode (Q := Q)]
  [SampleableType F] [SampleableType Fˣ]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F F F Nat M))
  (bd : Boundary C (ListROM.NativeInterface.sourceSpec F F M).toPFunctor F (M × F × F))
  (boundary : ListROM.NativePass.DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat M cost).execute instr))
  (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (ports : ListROM.NativeInterface.Ports (Q := Q) rep bd)
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : RawTape.NativePrivate.Ports (Q := Q) rep (iface := iface))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (fieldLaw : fieldSampler.denote () = ($ᵗ F : ProbComp F))
  (nonzeroLaw : nonzeroSampler.denote () = (fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ))

example (bound : ExecutionCost) (runs : R.RunsWithin (fun _ => bound))
    (fuel qH : Nat) (enough : bound.queries ≤ fuel)
    (implementation : R.machine.Implements adaptiveMain) (g pk : F) :
    (NonzeroListROM.NativeSolver.code rep bd boundary data cost primitive fieldSampler nonzeroSampler
      ports uniform privatePorts R fuel qH).denote (g, pk, ()) =
      NonzeroListROM.NativeSolver.reduction (G₂ := F) (K := Nat) adaptiveMain qH g pk :=
  NonzeroListROM.NativeSolver.source_of_resources rep bd boundary data cost primitive fieldSampler nonzeroSampler
    ports uniform privatePorts R fieldLaw nonzeroLaw bound runs fuel qH enough adaptiveMain implementation g pk

end Source

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``NonzeroListROM.NativePass.TimeInputs.time_polynomial,
      ``NonzeroListROM.NativePass.Resources.tapeWidth_le,
      ``NonzeroListROM.NativePass.Resources.fieldSampler_bound,
      ``NonzeroListROM.NativePass.Resources.pass_bound,
      ``NonzeroListROM.NativeROMFork.source_of_resources,
      ``NonzeroListROM.NativeROMFork.result_shape_of_resources,
      ``NonzeroListROM.NativeROMFork.code_description,
      ``NonzeroListROM.NativeROMFork.code_bound_of_resources,
      ``NonzeroListROM.NativeROMFork.resourcesTime_polynomial,
      ``NonzeroListROM.NativeSolver.code_denote, ``NonzeroListROM.NativeSolver.source_of_resources,
      ``NonzeroListROM.NativeSolver.source_reduction, ``NonzeroListROM.NativeSolver.code_description,
      ``NonzeroListROM.NativeSolver.code_bound_of_resources, ``NonzeroListROM.NativeSolver.resourcesTime_polynomial,
      ``NonzeroListROM.NativeSolver.codeDescription_eq,
      ``NonzeroListROM.NativeSolver.DescriptionInputs.solver_le_common,
      ``NonzeroListROM.NativeSolver.DescriptionInputs.solver_polynomial,
      ``NonzeroListROM.NativeSolver.DescriptionInputs.compiled_polynomial,
      ``NonzeroListROM.NativeSolver.DescriptionInputs.solver_withCaller,
      ``NonzeroListROM.NativeSolver.reduction_at_generator, ``NonzeroListROM.NativeSolver.reduction_experiment,
      ``NonzeroListROM.NativeSolver.program_within, ``NonzeroListROM.NativeSolver.security_of_resources] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``NonzeroListROM.NativeROMFork.code_bound_of_resources,
      ``NonzeroListROM.NativeSolver.code_bound_of_resources, ``NonzeroListROM.NativeSolver.program_within] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      let mut measured := false
      let mut resources := #[]
      for param in params do
        let type ← inferType param
        if (type.find? (fun e => e.isConstOf ``QuantitativeRealization.RunsWithin)).isSome then
          measured := true
        if type.isAppOf ``NonzeroListROM.NativePass.Resources then
          resources := resources.push (← getFVarLocalDecl param).userName
        for forbidden in #[``Within, ``Bounds, ``GeneralCaller.Budget, ``Program, ``SourceCertificate,
            ``Fintype, ``Finite, ``Inhabited, ``ListROM.NativePass.Resources] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: derive actual nonzero components from original resources"
      unless measured && resources == #[`first, `second] do
        throwError "{name}: require measured arbitrary attacker and separate original first/replay resources"
      if name == ``NonzeroListROM.NativeSolver.program_within then
        unless conclusion.isAppOf ``Within do
          throwError "Construct the executable fixed-backend witness"
        for required in #[``NonzeroListROM.NativeSolver.DescriptionInputs.solver,
            ``NonzeroListROM.NativeSolver.resourcesTime, ``NonzeroListROM.NativeSolver.reduction] do
          unless (conclusion.find? (fun e => e.isConstOf required)).isSome do
            throwError "Certificate must describe the actual nonzero reduction and complete code/time formulas"
      else
        unless conclusion.isAppOf ``Bounds do
          throwError "Derive complete execution bounds, including returned encodings"
  forallTelescope (← getConstInfo ``NonzeroListROM.NativePass.Resources.mk).type fun params _ => do
    let mut profiles := #[]
    let mut nonzeroCount := none
    let mut reservation := none
    for param in params do
      let type ← inferType param
      let userName := (← getFVarLocalDecl param).userName
      if type.isAppOf ``ExecutionProfile.Within then
        profiles := profiles.push userName
      if userName == `nonzeroQueries then nonzeroCount := some param
      if userName == `hsaved then reservation := some type
      for forbidden in #[``Bounds, ``Within, ``GeneralCaller.Budget, ``Program, ``SourceCertificate,
          ``NonzeroListROM.NativePass.code, ``NonzeroListROM.NativeHandler.code,
          ``NonzeroListROM.NativeHandler.timeBudget, ``ListROM.NativePass.timeBudget] do
        if (type.find? (fun e => e.isConstOf forbidden)).isSome then
          throwError "The resource record must package original contracts only"
    unless profiles == #[`fieldProfile, `nonzeroProfile] do
      throwError "Preserve both original sampler execution profiles"
    let some count := nonzeroCount | throwError "Missing nonzero sampler query count"
    let some capacity := reservation | throwError "Missing full-run reservation"
    unless (capacity.find? (fun e => e == count)).isSome do
      throwError "Every full-run reservation must include the additional sampler queries"
  for name in #[``NonzeroListROM.NativeROMFork.source_of_resources,
      ``NonzeroListROM.NativeSolver.source_of_resources, ``NonzeroListROM.NativeSolver.source_reduction] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      unless conclusion.isAppOf ``Eq do
        throwError "Require equality of the entire computation, not just a marginal success probability"
      for param in params do
        let type ← inferType param
        for forbidden in #[``Bounds, ``Within, ``Program, ``SourceCertificate, ``Fintype, ``Finite, ``Inhabited] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "Keep arbitrary implemented attackers and arbitrary message domains"
      if name == ``NonzeroListROM.NativeSolver.source_reduction then
        unless (conclusion.find? (fun e => e.isConstOf ``_root_.Schnorr.NonzeroNonce.LazyROM.dlogReduction)).isSome do
          throwError "Connect to the original nonzero-nonce security reduction"
      else
        unless (conclusion.find? (fun e => e.isConstOf ``NonzeroListROM.pass)).isSome do
          throwError "Both replayed executions must use the nonzero pass"
  for (name, required, forbidden) in #[(
      ``NonzeroListROM.NativeROMFork.code, ``NonzeroListROM.NativePass.code, ``ListROM.NativePass.code),
      (``NonzeroListROM.NativeSolver.code, ``NonzeroListROM.NativeROMFork.code, ``ListROM.NativeROMFork.code)] do
    let .defnInfo info ← getConstInfo name | throwError "Expected actual executed code"
    unless (info.value.find? (fun e => e.isConstOf required)).isSome do
      throwError "Install the actual nonzero implementation"
    if (info.value.find? (fun e => e.isConstOf forbidden)).isSome then
      throwError "Do not substitute the full-field pass or fork"
  let .defnInfo solver ← getConstInfo ``NonzeroListROM.NativeSolver.code | throwError "Expected solver code"
  unless (solver.value.find? (fun e => e.isConstOf ``ListROM.NativeExtraction.code)).isSome do
    throwError "Execute the proved guarded extraction and both fallback paths"
  for name in #[``NonzeroListROM.NativePass.TimeInputs.time_polynomial,
      ``NonzeroListROM.NativeROMFork.resourcesTime_polynomial, ``NonzeroListROM.NativeSolver.resourcesTime_polynomial,
      ``NonzeroListROM.NativeSolver.DescriptionInputs.solver_polynomial,
      ``NonzeroListROM.NativeSolver.DescriptionInputs.compiled_polynomial] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      unless conclusion.isAppOf ``PolynomiallyBounded do
        throwError "Derive polynomial closure for the actual complete formula"
      for param in params do
        let type ← inferType param
        if #[`counter, `arityCap, `domainSize].contains (← getFVarLocalDecl param).userName then
          throwError "No polynomial numerical arity, counter or universe-size premise"
        for forbidden in #[``NonzeroListROM.NativePass.TimeInputs.time,
            ``NonzeroListROM.NativeROMFork.resourcesTime, ``NonzeroListROM.NativeSolver.resourcesTime,
            ``NonzeroListROM.NativeSolver.DescriptionInputs.solver, ``Bounds, ``Within] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "Derive finished polynomial bounds from original input families"
  forallTelescope (← getConstInfo ``NonzeroListROM.NativeSolver.security_of_resources).type fun params conclusion => do
    for required in #[``_root_.Schnorr.NonzeroNonce.game] do
      unless (conclusion.find? (fun e => e.isConstOf required)).isSome do
        throwError "Preserve the actual nonzero game and its card(F)-1 signing loss"
    unless (conclusion.find? (fun e => e.isAppOfArity ``HSub.hSub 6 &&
        (e.getArg! 0).isConstOf ``Nat)).isSome do
      throwError "Preserve subtraction in Nat in the nonzero signing denominator"
    let mut fixedHardness := false
    for param in params do
      let type ← inferType param
      if (type.find? (fun e => e.isConstOf ``Model.HardWithin)).isSome then
        fixedHardness := (type.find? (fun e => e.isConstOf ``ListROM.NativeSolver.dlogWithin)).isSome
      for forbidden in #[``Within, ``Bounds, ``Program, ``SourceCertificate] do
        if (type.find? (fun e => e.isConstOf forbidden)).isSome then
          throwError "Construct the solver certificate before applying hardness"
    unless fixedHardness do
      throwError "Use DLog hardness for the same fixed backend and complete budgets"

end SignaturesTest.SchnorrNonzeroSolver
