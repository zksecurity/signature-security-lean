import Signatures.Runtime.BackendWeightedSolverBudget
import Signatures.Runtime.BackendWeightedSolverDescription
import Signatures.Runtime.PolynomialResources

/-! Polynomial closure of the actual weighted native solver budgets. Degree or
vector dimension, caller resources, encoding widths and individual operation
prices may vary with the security parameter. No message-domain size or completed
solver efficiency premise is used. The closure proofs also charge stored code. -/

namespace Signatures.Runtime.WeightedAGM

open PFunctor BackendProgram NativeHandler

private theorem max_polynomial {f g : Nat → Nat}
    (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => max (f n) (g n)) :=
  (hf.add hg).of_le (fun _ => Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩)

private theorem cases_polynomial (index : Nat → Index) (f g : Nat → Nat → Nat)
    (hf : PolynomiallyBounded (fun n => f n (index n).bound))
    (hg : PolynomiallyBounded (fun n => g n (index n).bound)) :
    PolynomiallyBounded (fun n => match index n with
      | .oops d => f n d | .proximity d => g n d) := by
  apply (hf.add hg).of_le
  intro n
  cases index n <;> simp only [Index.bound] <;> omega

-- Choose a closure rule from the displayed constructor, or unfold one numeric
-- cost definition. This avoids higher-order backtracking over large cost formulas.
-- Every result is a kernel-checked application of an ordinary closure theorem.
open Lean Meta Elab Tactic in
local elab "polynomial_step" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``PolynomiallyBounded do
    throwError "expected a polynomial resource bound"
  let resource := target.getAppArgs[0]!
  let (rule, expanded) ← withLocalDeclD `parameter (mkConst ``Nat) fun parameter => do
    let mut body := (mkApp resource parameter).headBeta.consumeMData
    while let .letE _ _ value letBody _ := body do
      body := (letBody.instantiate1 value).headBeta.consumeMData
    let rule? := if body.isAppOf ``HAdd.hAdd || body.isAppOf ``Nat.add then
        some ``PolynomiallyBounded.add
      else if body.isAppOf ``HMul.hMul || body.isAppOf ``Nat.mul then
        some ``PolynomiallyBounded.mul
      else if body.isAppOf ``Max.max || body.isAppOf ``Nat.max then
        some ``max_polynomial
      else if body.isAppOf ``Finset.sum then
        some ``PolynomiallyBounded.sum
      else if (body.find? (· == parameter)).isNone then
        some ``PolynomiallyBounded.const
      else if body.getAppFn.isFVar && body.getAppNumArgs == 2 then
        some ``PolynomialOverhead.apply
      else none
    if let some rule := rule? then return (some rule, none)
    if let .const name _ := body.getAppFn then
      let proofName := name.appendAfter "_polynomial"
      if (← getEnv).contains proofName then return (some proofName, none)
    let some expanded ← unfoldDefinition? body (ignoreTransparency := true)
      | throwError "no polynomial closure rule for {body}"
    return (none, some (← mkLambdaFVars #[parameter] expanded))
  if let some rule := rule then
    replaceMainGoal (← (← getMainGoal).apply (← mkConstWithFreshMVarLevels rule))
  else if let some expanded := expanded then
    replaceMainGoal [← (← getMainGoal).replaceTargetDefEq (mkApp target.getAppFn expanded)]

local macro "polynomial_bound" : tactic =>
  `(tactic| repeat' first | assumption | intro i | polynomial_step)

theorem Index.termsTime_polynomial (index : Nat → Index) (overhead : Nat → Nat → Nat)
    (width indexTime mulTime finZeroTime oneTime : Nat → Nat)
    (hIndex : PolynomiallyBounded (fun n => (index n).bound))
    (hOverhead : PolynomialOverhead overhead)
    (hWidth : PolynomiallyBounded width)
    (hIndexTime : PolynomiallyBounded indexTime)
    (hMulTime : PolynomiallyBounded mulTime)
    (hFinZeroTime : PolynomiallyBounded finZeroTime)
    (hOneTime : PolynomiallyBounded oneTime)
    : PolynomiallyBounded (fun n => (index n).termsTime (overhead n)
      (width n) (indexTime n) (mulTime n) (finZeroTime n) (oneTime n)) := by
  unfold Index.termsTime
  apply cases_polynomial
  · polynomial_bound
  · polynomial_bound

theorem Index.coefficientTime_polynomial (index : Nat → Index) (overhead : Nat → Nat → Nat)
    (width tokenCap coeffCap indexTime finZeroTime oneTime mulTime natEqTime natSubTime natAddTime zeroTime : Nat → Nat)
    (hIndex : PolynomiallyBounded (fun n => (index n).bound))
    (hOverhead : PolynomialOverhead overhead)
    (hWidth : PolynomiallyBounded width)
    (hTokenCap : PolynomiallyBounded tokenCap)
    (hCoeffCap : PolynomiallyBounded coeffCap)
    (hIndexTime : PolynomiallyBounded indexTime)
    (hFinZeroTime : PolynomiallyBounded finZeroTime)
    (hOneTime : PolynomiallyBounded oneTime)
    (hMulTime : PolynomiallyBounded mulTime)
    (hNatEqTime : PolynomiallyBounded natEqTime)
    (hNatSubTime : PolynomiallyBounded natSubTime)
    (hNatAddTime : PolynomiallyBounded natAddTime)
    (hZeroTime : PolynomiallyBounded zeroTime)
    : PolynomiallyBounded (fun n => (index n).coefficientTime (overhead n)
      (width n) (tokenCap n) (coeffCap n) (indexTime n) (finZeroTime n) (oneTime n) (mulTime n) (natEqTime n) (natSubTime n) (natAddTime n) (zeroTime n)) := by
  unfold Index.coefficientTime
  apply cases_polynomial
  · polynomial_bound
  · polynomial_bound

theorem NativeHandler.goodHandlerTime_polynomial (index : Nat → Index) (overhead : Nat → Nat → Nat)
    (width cap comparisonTime scalarTime opTime tickTime adapterTime dynamicTime : Nat → Nat)
    (hIndex : PolynomiallyBounded (fun n => (index n).bound))
    (hOverhead : PolynomialOverhead overhead)
    (hWidth : PolynomiallyBounded width)
    (hCap : PolynomiallyBounded cap)
    (hComparisonTime : PolynomiallyBounded comparisonTime)
    (hScalarTime : PolynomiallyBounded scalarTime)
    (hOpTime : PolynomiallyBounded opTime)
    (hTickTime : PolynomiallyBounded tickTime)
    (hAdapterTime : PolynomiallyBounded adapterTime)
    (hDynamicTime : PolynomiallyBounded dynamicTime)
    : PolynomiallyBounded (fun n => NativeHandler.goodHandlerTime (index n) (overhead n)
      (width n) (cap n) (opTime n) (opTime n) (opTime n) (comparisonTime n) (opTime n) (scalarTime n) (opTime n) (opTime n) (opTime n) (tickTime n) (opTime n) (opTime n) (opTime n) (opTime n) (adapterTime n) (dynamicTime n)) := by
  dsimp only [NativeHandler.goodHandlerTime]
  polynomial_bound

theorem NativeHandler.badHandlerTime_polynomial (index : Nat → Index) (overhead : Nat → Nat → Nat)
    (width cap comparisonTime scalarTime opTime tickTime adapterTime dynamicTime : Nat → Nat)
    (hIndex : PolynomiallyBounded (fun n => (index n).bound))
    (hOverhead : PolynomialOverhead overhead)
    (hWidth : PolynomiallyBounded width)
    (hCap : PolynomiallyBounded cap)
    (hComparisonTime : PolynomiallyBounded comparisonTime)
    (hScalarTime : PolynomiallyBounded scalarTime)
    (hOpTime : PolynomiallyBounded opTime)
    (hTickTime : PolynomiallyBounded tickTime)
    (hAdapterTime : PolynomiallyBounded adapterTime)
    (hDynamicTime : PolynomiallyBounded dynamicTime)
    : PolynomiallyBounded (fun n => NativeHandler.badHandlerTime (index n) (overhead n)
      (width n) (cap n) (opTime n) (opTime n) (opTime n) (comparisonTime n) (opTime n) (scalarTime n) (opTime n) (opTime n) (opTime n) (tickTime n) (opTime n) (opTime n) (opTime n) (opTime n) (opTime n) (adapterTime n) (dynamicTime n)) := by
  dsimp only [NativeHandler.badHandlerTime]
  polynomial_bound

theorem Extract.goodExtractionTime_polynomial (index : Nat → Index) (overhead : Nat → Nat → Nat)
    (width hashCap signCap coeffCap cacheCap comparisonTime scalarTime opTime tickTime : Nat → Nat)
    (hIndex : PolynomiallyBounded (fun n => (index n).bound))
    (hOverhead : PolynomialOverhead overhead)
    (hWidth : PolynomiallyBounded width)
    (hHashCap : PolynomiallyBounded hashCap)
    (hSignCap : PolynomiallyBounded signCap)
    (hCoeffCap : PolynomiallyBounded coeffCap)
    (hCacheCap : PolynomiallyBounded cacheCap)
    (hComparisonTime : PolynomiallyBounded comparisonTime)
    (hScalarTime : PolynomiallyBounded scalarTime)
    (hOpTime : PolynomiallyBounded opTime)
    (hTickTime : PolynomiallyBounded tickTime)
    : PolynomiallyBounded (fun n => Extract.goodExtractionTime (index n) (overhead n)
      (width n) (hashCap n) (signCap n) (coeffCap n) (cacheCap n) (opTime n) (opTime n) (opTime n) (comparisonTime n) (opTime n) (scalarTime n) (opTime n) (opTime n) (opTime n) (tickTime n) (opTime n) (opTime n) (opTime n) (opTime n) (opTime n)) := by
  dsimp only [Extract.goodExtractionTime]
  polynomial_bound

theorem Extract.badExtractionTime_polynomial (index : Nat → Index) (overhead : Nat → Nat → Nat)
    (width hashCap signCap coeffCap cacheCap comparisonTime scalarTime opTime tickTime : Nat → Nat)
    (hIndex : PolynomiallyBounded (fun n => (index n).bound))
    (hOverhead : PolynomialOverhead overhead)
    (hWidth : PolynomiallyBounded width)
    (hHashCap : PolynomiallyBounded hashCap)
    (hSignCap : PolynomiallyBounded signCap)
    (hCoeffCap : PolynomiallyBounded coeffCap)
    (hCacheCap : PolynomiallyBounded cacheCap)
    (hComparisonTime : PolynomiallyBounded comparisonTime)
    (hScalarTime : PolynomiallyBounded scalarTime)
    (hOpTime : PolynomiallyBounded opTime)
    (hTickTime : PolynomiallyBounded tickTime)
    : PolynomiallyBounded (fun n => Extract.badExtractionTime (index n) (overhead n)
      (width n) (hashCap n) (signCap n) (coeffCap n) (cacheCap n) (opTime n) (opTime n) (opTime n) (comparisonTime n) (opTime n) (scalarTime n) (opTime n) (opTime n) (opTime n) (tickTime n) (opTime n) (opTime n) (opTime n) (opTime n) (opTime n) (opTime n)) := by
  dsimp only [Extract.badExtractionTime]
  polynomial_bound

namespace NativeSolver

section Program

variable (index : Nat → Index) (overhead : Nat → Nat → Nat) (bound : Nat → ExecutionCost)
  (inputWidth width outputWidth routeWidth cap fuel comparisonTime scalarTime opTime handlerAdapterTime solverAdapterTime dynamicTime handlerTickTime callerTickTime extractionTickTime : Nat → Nat)
  (hIndex : PolynomiallyBounded (fun n => (index n).bound))
  (hOverhead : PolynomialOverhead overhead)
  (hWork : PolynomiallyBounded (fun n => (bound n).work))
  (hQueries : PolynomiallyBounded (fun n => (bound n).queries))
  (hInputWidth : PolynomiallyBounded inputWidth)
  (hWidth : PolynomiallyBounded width)
  (hOutputWidth : PolynomiallyBounded outputWidth)
  (hRouteWidth : PolynomiallyBounded routeWidth)
  (hCap : PolynomiallyBounded cap)
  (hFuel : PolynomiallyBounded fuel)
  (hComparisonTime : PolynomiallyBounded comparisonTime)
  (hScalarTime : PolynomiallyBounded scalarTime)
  (hOpTime : PolynomiallyBounded opTime)
  (hHandlerAdapterTime : PolynomiallyBounded handlerAdapterTime)
  (hSolverAdapterTime : PolynomiallyBounded solverAdapterTime)
  (hDynamicTime : PolynomiallyBounded dynamicTime)
  (hHandlerTickTime : PolynomiallyBounded handlerTickTime)
  (hCallerTickTime : PolynomiallyBounded callerTickTime)
  (hExtractionTickTime : PolynomiallyBounded extractionTickTime)

include hIndex hOverhead hWork hQueries hInputWidth hWidth hOutputWidth hRouteWidth hCap hFuel hComparisonTime hScalarTime hOpTime hHandlerAdapterTime hSolverAdapterTime hDynamicTime hHandlerTickTime hCallerTickTime hExtractionTickTime

theorem goodProgramTime_polynomial :
    PolynomiallyBounded (fun n => goodProgramTime (index n) (overhead n) (bound n)
      (inputWidth n) (width n) (outputWidth n) (routeWidth n) (cap n) (fuel n) (comparisonTime n) (scalarTime n) (opTime n) (handlerAdapterTime n) (solverAdapterTime n) (dynamicTime n) (handlerTickTime n) (callerTickTime n) (extractionTickTime n)) := by
  dsimp only [goodProgramTime]
  polynomial_bound

theorem badProgramTime_polynomial :
    PolynomiallyBounded (fun n => badProgramTime (index n) (overhead n) (bound n)
      (inputWidth n) (width n) (outputWidth n) (routeWidth n) (cap n) (fuel n) (comparisonTime n) (scalarTime n) (opTime n) (handlerAdapterTime n) (solverAdapterTime n) (dynamicTime n) (handlerTickTime n) (callerTickTime n) (extractionTickTime n)) := by
  dsimp only [badProgramTime]
  polynomial_bound

end Program

theorem programDescription_polynomial
    (factor degree caller scalarSampler dynamicSampler fuel allowance instruction handlerPort solverPort : Nat → Nat)
    (hFactor : PolynomiallyBounded factor)
    (hDegree : PolynomiallyBounded degree)
    (hCaller : PolynomiallyBounded caller)
    (hScalarSampler : PolynomiallyBounded scalarSampler)
    (hDynamicSampler : PolynomiallyBounded dynamicSampler)
    (hFuel : PolynomiallyBounded fuel)
    (hAllowance : PolynomiallyBounded allowance)
    (hInstruction : PolynomiallyBounded instruction)
    (hHandlerPort : PolynomiallyBounded handlerPort)
    (hSolverPort : PolynomiallyBounded solverPort)
    : PolynomiallyBounded (fun n => factor n * programDescription (degree n) (caller n)
      (scalarSampler n) (dynamicSampler n) (fuel n) (allowance n) (instruction n) (handlerPort n) (solverPort n)) := by
  polynomial_bound

end NativeSolver

end Signatures.Runtime.WeightedAGM
