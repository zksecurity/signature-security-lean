import Signatures.Runtime.BackendLazyAGMSolverBudget
import Signatures.Runtime.BackendLazyAGMSolverDescription
import Signatures.Runtime.PolynomialResources

/-! Polynomial closure of the complete native BLS AGM solver budgets. The
inputs are bounds on caller resources, encodings and individual operations.
The output concerns the actual derived runtime and stored-code formulas, with
one fixed polynomial across security parameters. No message domain is counted. -/

open PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram NativeHandler

-- Select the closure rule by the displayed arithmetic constructor. Blind
-- backtracking through higher-order addition goals revisits the large formulas.
open Lean Meta Elab Tactic in
local elab "polynomial_step" : tactic => do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``PolynomiallyBounded do
    throwError "expected a polynomial resource bound"
  let resource := target.getAppArgs[0]!
  let rule ← withLocalDeclD `parameter (mkConst ``Nat) fun parameter => do
    let body := (mkApp resource parameter).headBeta
    if body.isAppOf ``HAdd.hAdd || body.isAppOf ``Nat.add then
      pure ``PolynomiallyBounded.add
    else if body.isAppOf ``HMul.hMul || body.isAppOf ``Nat.mul then
      pure ``PolynomiallyBounded.mul
    else if (body.find? (· == parameter)).isNone then
      pure ``PolynomiallyBounded.const
    else if body.getAppNumArgs == 2 then
      pure ``PolynomialOverhead.apply
    else
      throwError "no polynomial closure rule for {body}"
  let goals ← (← getMainGoal).apply (← mkConstWithFreshMVarLevels rule)
  replaceMainGoal goals

local macro "polynomial_bound" : tactic =>
  `(tactic| repeat' first | assumption | polynomial_step)

section Components

variable (overhead : Nat → Nat → Nat)
  (width cap coeffCap cacheCap comparisonTime scalarTime opTime tickTime : Nat → Nat)
  (hOverhead : PolynomialOverhead overhead)
  (hWidth : PolynomiallyBounded width) (hCap : PolynomiallyBounded cap)
  (hCoeff : PolynomiallyBounded coeffCap) (hCache : PolynomiallyBounded cacheCap)
  (hCompare : PolynomiallyBounded comparisonTime) (hScalar : PolynomiallyBounded scalarTime)
  (hOp : PolynomiallyBounded opTime) (hTick : PolynomiallyBounded tickTime)

include hOverhead hWidth hCap hCoeff hCache hCompare hScalar hOp hTick

theorem goodTokenTime_polynomial :
    PolynomiallyBounded (fun n => goodTokenTime (overhead n) (width n) (cap n) (coeffCap n) (cacheCap n)
      (opTime n) (opTime n) (opTime n) (comparisonTime n) (scalarTime n)
      (opTime n) (opTime n) (opTime n) (tickTime n)) := by
  dsimp only [goodTokenTime, TokenCompiler.rowsTime, TokenCompiler.rowsWidth,
    AttachCompiler.tableWidth, AttachCompiler.frameWidth, evaluationWidth, tokenFrameWidth, CacheCompiler.frameWidth]
  polynomial_bound

theorem badTokenTime_polynomial :
    PolynomiallyBounded (fun n => badTokenTime (overhead n) (width n) (cap n) (coeffCap n) (cacheCap n)
      (opTime n) (opTime n) (opTime n) (comparisonTime n) (scalarTime n)
      (opTime n) (opTime n) (opTime n) (tickTime n)) := by
  dsimp only [badTokenTime, TokenCompiler.rowsTime, TokenCompiler.rowsWidth,
    AttachCompiler.tableWidth, AttachCompiler.frameWidth, evaluationWidth, tokenFrameWidth, CacheCompiler.frameWidth]
  polynomial_bound

theorem goodExtractionTime_polynomial :
    PolynomiallyBounded (fun n => goodExtractionTime (overhead n) (width n) (cap n) (coeffCap n) (cacheCap n)
      (opTime n) (opTime n) (opTime n) (comparisonTime n) (scalarTime n)
      (opTime n) (opTime n) (opTime n) (opTime n) (opTime n) (opTime n) (tickTime n)) := by
  have hTokens := goodTokenTime_polynomial overhead (fun n => 5 * width n) cap coeffCap cacheCap
    comparisonTime scalarTime opTime tickTime hOverhead ((PolynomiallyBounded.const 5).mul hWidth)
    hCap hCoeff hCache hCompare hScalar hOp hTick
  have hTokens' := goodTokenTime_polynomial overhead (fun n => 5 * width n) cap coeffCap
    (fun n => cacheCap n + cap n) comparisonTime scalarTime opTime tickTime hOverhead
    ((PolynomiallyBounded.const 5).mul hWidth) hCap hCoeff (hCache.add hCap) hCompare hScalar hOp hTick
  dsimp only [goodExtractionTime, extractionWidth, tokenFrameWidth, evaluationWidth, CacheCompiler.frameWidth]
  polynomial_bound

theorem badExtractionTime_polynomial :
    PolynomiallyBounded (fun n => badExtractionTime (overhead n) (width n) (cap n) (coeffCap n) (cacheCap n)
      (opTime n) (opTime n) (opTime n) (comparisonTime n) (scalarTime n)
      (opTime n) (opTime n) (opTime n) (opTime n) (opTime n) (opTime n) (opTime n) (tickTime n)) := by
  have hTokens := badTokenTime_polynomial overhead (fun n => 5 * width n) cap coeffCap cacheCap
    comparisonTime scalarTime opTime tickTime hOverhead ((PolynomiallyBounded.const 5).mul hWidth)
    hCap hCoeff hCache hCompare hScalar hOp hTick
  dsimp only [badExtractionTime, extractionWidth, tokenFrameWidth, evaluationWidth, CacheCompiler.frameWidth]
  polynomial_bound

end Components

namespace NativeSolver

section Program

variable (overhead : Nat → Nat → Nat) (bound : Nat → ExecutionCost)
  (inputWidth width outputWidth routeWidth cap fuel comparisonTime scalarTime opTime
    handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime : Nat → Nat)
  (hOverhead : PolynomialOverhead overhead)
  (hWork : PolynomiallyBounded (fun n => (bound n).work))
  (hQueries : PolynomiallyBounded (fun n => (bound n).queries))
  (hInput : PolynomiallyBounded inputWidth) (hWidth : PolynomiallyBounded width)
  (hOutput : PolynomiallyBounded outputWidth) (hRoute : PolynomiallyBounded routeWidth)
  (hCap : PolynomiallyBounded cap) (hFuel : PolynomiallyBounded fuel)
  (hCompare : PolynomiallyBounded comparisonTime) (hScalar : PolynomiallyBounded scalarTime)
  (hOp : PolynomiallyBounded opTime) (hHandler : PolynomiallyBounded handlerAdapterTime)
  (hSolver : PolynomiallyBounded solverAdapterTime) (hDynamic : PolynomiallyBounded dynamicTime)
  (hCallerTick : PolynomiallyBounded callerTickTime) (hExtractionTick : PolynomiallyBounded extractionTickTime)

include hOverhead hWork hQueries hInput hWidth hOutput hRoute hCap hFuel
  hCompare hScalar hOp hHandler hSolver hDynamic hCallerTick hExtractionTick

theorem goodProgramTime_polynomial :
    PolynomiallyBounded (fun n => goodProgramTime (overhead n) (bound n)
      (inputWidth n) (width n) (outputWidth n) (routeWidth n) (cap n) (fuel n)
      (comparisonTime n) (scalarTime n) (opTime n) (handlerAdapterTime n) (solverAdapterTime n)
      (dynamicTime n) (callerTickTime n) (extractionTickTime n)) := by
  have hTerminalInput : PolynomiallyBounded (fun n => terminalInputWidth (width n) (outputWidth n) (cap n)) := by
    dsimp only [terminalInputWidth, handlerStoreWidth]
    polynomial_bound
  have hExtraction := goodExtractionTime_polynomial overhead _ cap outputWidth cap comparisonTime scalarTime
    opTime extractionTickTime hOverhead hTerminalInput hCap hOutput hCap hCompare hScalar hOp hExtractionTick
  have hHandlerTime : PolynomiallyBounded (fun n => goodHandlerTime (overhead n) (width n) (cap n)
      (comparisonTime n) (scalarTime n) (opTime n) (opTime n) (handlerAdapterTime n) (dynamicTime n)) := by
    dsimp only [goodHandlerTime, goodReplyTime, SignatureHandler.handlerTime, handlerStoreWidth,
      replyWidth, CacheCompiler.frameWidth]
    polynomial_bound
  have hCalls := PolynomiallyBounded.sum
    (fun (_ : Fin 3) n => (bound n).queries * goodHandlerTime (overhead n) (width n) (cap n)
      (comparisonTime n) (scalarTime n) (opTime n) (opTime n) (handlerAdapterTime n) (dynamicTime n))
    (fun _ => hQueries.mul hHandlerTime)
  dsimp only [goodProgramTime, SignatureHandler.callerTime, goodTerminalTime, setupWidth,
    programJoinWidth, terminalFrameWidth, terminalInputWidth, handlerStoreWidth,
    extractionWidth, tokenFrameWidth, evaluationWidth]
  polynomial_bound

theorem badProgramTime_polynomial :
    PolynomiallyBounded (fun n => badProgramTime (overhead n) (bound n)
      (inputWidth n) (width n) (outputWidth n) (routeWidth n) (cap n) (fuel n)
      (comparisonTime n) (scalarTime n) (opTime n) (handlerAdapterTime n) (solverAdapterTime n)
      (dynamicTime n) (callerTickTime n) (extractionTickTime n)) := by
  have hTerminalInput : PolynomiallyBounded (fun n => terminalInputWidth (width n) (outputWidth n) (cap n)) := by
    dsimp only [terminalInputWidth, handlerStoreWidth]
    polynomial_bound
  have hExtraction := badExtractionTime_polynomial overhead _ cap outputWidth cap comparisonTime scalarTime
    opTime extractionTickTime hOverhead hTerminalInput hCap hOutput hCap hCompare hScalar hOp hExtractionTick
  have hHandlerTime : PolynomiallyBounded (fun n => badHandlerTime (overhead n) (width n) (cap n)
      (comparisonTime n) (scalarTime n) (opTime n) (opTime n) (opTime n) (handlerAdapterTime n) (dynamicTime n)) := by
    dsimp only [badHandlerTime, badReplyTime, SignatureHandler.handlerTime, handlerStoreWidth,
      replyWidth, CacheCompiler.frameWidth]
    polynomial_bound
  have hCalls := PolynomiallyBounded.sum
    (fun (_ : Fin 3) n => (bound n).queries * badHandlerTime (overhead n) (width n) (cap n)
      (comparisonTime n) (scalarTime n) (opTime n) (opTime n) (opTime n) (handlerAdapterTime n) (dynamicTime n))
    (fun _ => hQueries.mul hHandlerTime)
  dsimp only [badProgramTime, SignatureHandler.callerTime, badTerminalTime, setupWidth,
    programJoinWidth, terminalFrameWidth, terminalInputWidth, handlerStoreWidth,
    extractionWidth, tokenFrameWidth, evaluationWidth]
  polynomial_bound

end Program

theorem programDescription_polynomial
    (factor caller scalarSampler dynamicSampler fuel allowance instruction handlerPort solverPort : Nat → Nat)
    (hFactor : PolynomiallyBounded factor) (hCaller : PolynomiallyBounded caller)
    (hScalar : PolynomiallyBounded scalarSampler) (hDynamic : PolynomiallyBounded dynamicSampler)
    (hFuel : PolynomiallyBounded fuel) (hAllowance : PolynomiallyBounded allowance)
    (hInstruction : PolynomiallyBounded instruction) (hHandler : PolynomiallyBounded handlerPort)
    (hSolver : PolynomiallyBounded solverPort) :
    PolynomiallyBounded (fun n => factor n * programDescription (caller n) (scalarSampler n)
      (dynamicSampler n) (fuel n) (allowance n) (instruction n) (handlerPort n) (solverPort n)) := by
  dsimp only [programDescription]
  polynomial_bound

end NativeSolver

end Signatures.Runtime.LazyAGM
