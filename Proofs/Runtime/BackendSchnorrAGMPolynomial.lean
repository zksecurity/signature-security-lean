import Proofs.Runtime.BackendSchnorrAGMSolverBudget
import Proofs.Runtime.BackendSchnorrAGMSolverDescription
import Proofs.Runtime.PolynomialResources

/-! Polynomial closure for the actual native Schnorr AGM runtime and code
formulas. Assumptions concern measured caller resources, encoded sizes and
individual operations. Neither the message universe nor numerical random arity
must be polynomial. Each resource has one fixed polynomial across parameters. -/

namespace Signatures.Runtime.SchnorrAGM.Native

open PFunctor

private theorem max_polynomial {f g : Nat → Nat}
    (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => max (f n) (g n)) :=
  (hf.add hg).of_le (fun _ => Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩)

-- Select a closure rule by the arithmetic constructor, unfolding numeric cost
-- definitions as needed. Every generated proof uses kernel-checked closure lemmas.
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

/-- Polynomial prices for the individual handler operations and scalar sampling.
These are the same component allowances used by the concrete runtime theorem. -/
structure Handler.PolynomialTimes (times : Nat → Handler.Times) : Prop where
  comparisonTime : PolynomiallyBounded (fun n => (times n).comparisonTime)
  subtractTime : PolynomiallyBounded (fun n => (times n).subtractTime)
  incrementTime : PolynomiallyBounded (fun n => (times n).incrementTime)
  messageTime : PolynomiallyBounded (fun n => (times n).messageTime)
  pointTime : PolynomiallyBounded (fun n => (times n).pointTime)
  fieldTime : PolynomiallyBounded (fun n => (times n).fieldTime)
  mulTime : PolynomiallyBounded (fun n => (times n).mulTime)
  equalityTime : PolynomiallyBounded (fun n => (times n).equalityTime)
  pointZeroTime : PolynomiallyBounded (fun n => (times n).pointZeroTime)
  scaleTime : PolynomiallyBounded (fun n => (times n).scaleTime)
  groupTime : PolynomiallyBounded (fun n => (times n).groupTime)
  sampleTime : PolynomiallyBounded (fun n => (times n).sampleTime)
  randomRequestTime : PolynomiallyBounded (fun n => (times n).randomRequestTime)
  randomResponseTime : PolynomiallyBounded (fun n => (times n).randomResponseTime)
  drawTime : PolynomiallyBounded (fun n => (times n).drawTime)
  requestTime : PolynomiallyBounded (fun n => (times n).requestTime)
  tagTime : PolynomiallyBounded (fun n => (times n).tagTime)

theorem Flatten.flattenTime_polynomial (overhead : Nat → Nat → Nat)
    (width basisCap coeffCap : Nat → Nat) (times : Nat → Handler.Times)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hBasis : PolynomiallyBounded basisCap) (hCoefficients : PolynomiallyBounded coeffCap)
    (hTimes : Handler.PolynomialTimes times) :
    PolynomiallyBounded (fun n => Flatten.flattenTime (overhead n) (width n) (basisCap n) (coeffCap n)
      (times n).comparisonTime (times n).subtractTime (times n).incrementTime (times n).fieldTime
      (times n).mulTime (times n).fieldTime) := by
  have hFrame : PolynomiallyBounded (fun n => Flatten.frameWidth (width n) (basisCap n) (coeffCap n)) := by
    polynomial_bound
  rcases hTimes with ⟨hComparison, hSubtract, hIncrement, hMessage, hPoint, hField, hMul,
    hEquality, hPointZero, hScale, hGroup, hSample, hRandomRequest, hRandomResponse, hDraw, hRequest, hTag⟩
  unfold Flatten.flattenTime
  polynomial_bound

theorem Read.readTime_polynomial (overhead : Nat → Nat → Nat)
    (width cap historyWidth : Nat → Nat) (times : Nat → Handler.Times)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hCap : PolynomiallyBounded cap) (hHistory : PolynomiallyBounded historyWidth)
    (hTimes : Handler.PolynomialTimes times) :
    PolynomiallyBounded (fun n => Read.readTime (overhead n) (width n) (cap n) (historyWidth n)
      (times n).messageTime (times n).pointTime (times n).fieldTime (times n).equalityTime (times n).sampleTime) := by
  rcases hTimes with ⟨hComparison, hSubtract, hIncrement, hMessage, hPoint, hField, hMul,
    hEquality, hPointZero, hScale, hGroup, hSample, hRandomRequest, hRandomResponse, hDraw, hRequest, hTag⟩
  unfold Read.readTime
  polynomial_bound

theorem Hash.hashTime_polynomial (overhead : Nat → Nat → Nat)
    (width cap historyWidth basisCap coeffCap : Nat → Nat) (times : Nat → Handler.Times)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hCap : PolynomiallyBounded cap) (hHistory : PolynomiallyBounded historyWidth)
    (hBasis : PolynomiallyBounded basisCap) (hCoefficients : PolynomiallyBounded coeffCap)
    (hTimes : Handler.PolynomialTimes times) :
    PolynomiallyBounded (fun n => Hash.hashTime (overhead n) (width n) (cap n) (historyWidth n)
      (basisCap n) (coeffCap n) (times n).comparisonTime (times n).subtractTime (times n).incrementTime
      (times n).messageTime (times n).pointTime (times n).fieldTime (times n).mulTime
      (times n).equalityTime (times n).sampleTime) := by
  have hFrame : PolynomiallyBounded (fun n => Hash.frameWidth (width n) (cap n) (coeffCap n) (historyWidth n)) := by
    polynomial_bound
  unfold Hash.hashTime
  polynomial_bound

theorem Extraction.extractionTime_polynomial (overhead : Nat → Nat → Nat)
    (width cap historyWidth basisCap groupCap rowCap coeffCap divisionTime : Nat → Nat)
    (times : Nat → Handler.Times)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hCap : PolynomiallyBounded cap) (hHistory : PolynomiallyBounded historyWidth)
    (hBasis : PolynomiallyBounded basisCap) (hGroups : PolynomiallyBounded groupCap)
    (hRows : PolynomiallyBounded rowCap) (hCoefficients : PolynomiallyBounded coeffCap)
    (hDivision : PolynomiallyBounded divisionTime) (hTimes : Handler.PolynomialTimes times) :
    PolynomiallyBounded (fun n => Extraction.extractionTime (overhead n) (width n) (cap n) (historyWidth n)
      (basisCap n) (groupCap n) (rowCap n) (coeffCap n) (times n).comparisonTime (times n).subtractTime
      (times n).incrementTime (times n).messageTime (times n).pointTime (times n).fieldTime (times n).mulTime
      (times n).equalityTime (times n).sampleTime (divisionTime n) (times n).pointZeroTime) := by
  have hFrame : PolynomiallyBounded (fun n => Extraction.frameWidth
      (width n) (cap n) (historyWidth n) (groupCap n) (rowCap n) (coeffCap n)) := by
    polynomial_bound
  have hField := hTimes.fieldTime
  have hPointZero := hTimes.pointZeroTime
  unfold Extraction.extractionTime
  polynomial_bound

theorem Handler.timeBudget_polynomial (overhead : Nat → Nat → Nat)
    (width cap basisCap signedCap groupCap rowCap coeffCap portWidth : Nat → Nat)
    (times : Nat → Handler.Times)
    (hOverhead : PolynomialOverhead overhead)
    (hWidth : PolynomiallyBounded width) (hCap : PolynomiallyBounded cap)
    (hBasis : PolynomiallyBounded basisCap) (hSigned : PolynomiallyBounded signedCap)
    (hGroups : PolynomiallyBounded groupCap) (hRows : PolynomiallyBounded rowCap)
    (hCoefficients : PolynomiallyBounded coeffCap) (hPort : PolynomiallyBounded portWidth)
    (hTimes : Handler.PolynomialTimes times) :
    PolynomiallyBounded (fun n => Handler.timeBudget (overhead n) (width n) (cap n) (basisCap n)
      (signedCap n) (groupCap n) (rowCap n) (coeffCap n) (portWidth n) (times n)) := by
  have hTimes' := hTimes
  rcases hTimes with ⟨hComparison, hSubtract, hIncrement, hMessage, hPoint, hField, hMul,
    hEquality, hPointZero, hScale, hGroup, hSample, hRandomRequest, hRandomResponse, hDraw, hRequest, hTag⟩
  unfold Handler.timeBudget
  polynomial_bound

theorem Solver.terminalTime_polynomial (overhead : Nat → Nat → Nat)
    (width outputWidth routeWidth cap basisCap signedCap adapterTime divisionTime : Nat → Nat)
    (times : Nat → Handler.Times)
    (hOverhead : PolynomialOverhead overhead)
    (hWidth : PolynomiallyBounded width) (hOutput : PolynomiallyBounded outputWidth)
    (hRoute : PolynomiallyBounded routeWidth) (hCap : PolynomiallyBounded cap)
    (hBasis : PolynomiallyBounded basisCap) (hSigned : PolynomiallyBounded signedCap)
    (hAdapter : PolynomiallyBounded adapterTime) (hDivision : PolynomiallyBounded divisionTime)
    (hTimes : Handler.PolynomialTimes times) :
    PolynomiallyBounded (fun n => Solver.terminalTime (overhead n) (width n) (outputWidth n) (routeWidth n)
      (cap n) (basisCap n) (signedCap n) (adapterTime n) (times n).comparisonTime (times n).subtractTime
      (times n).incrementTime (times n).messageTime (times n).pointTime (times n).fieldTime (times n).mulTime
      (times n).equalityTime (times n).sampleTime (divisionTime n) (times n).pointZeroTime) := by
  have hField := hTimes.fieldTime
  unfold Solver.terminalTime
  polynomial_bound

theorem Solver.programTime_polynomial (overhead : Nat → Nat → Nat) (bound : Nat → ExecutionCost)
    (inputWidth width outputWidth routeWidth cap basisCap signedCap groupCap rowCap coeffCap portWidth
      fuel tickTime adapterTime divisionTime : Nat → Nat) (times : Nat → Handler.Times)
    (hOverhead : PolynomialOverhead overhead)
    (hWork : PolynomiallyBounded (fun n => (bound n).work))
    (hQueries : PolynomiallyBounded (fun n => (bound n).queries))
    (hInput : PolynomiallyBounded inputWidth) (hWidth : PolynomiallyBounded width)
    (hOutput : PolynomiallyBounded outputWidth) (hRoute : PolynomiallyBounded routeWidth)
    (hCap : PolynomiallyBounded cap) (hBasis : PolynomiallyBounded basisCap)
    (hSigned : PolynomiallyBounded signedCap) (hGroups : PolynomiallyBounded groupCap)
    (hRows : PolynomiallyBounded rowCap) (hCoefficients : PolynomiallyBounded coeffCap)
    (hPort : PolynomiallyBounded portWidth) (hFuel : PolynomiallyBounded fuel)
    (hTick : PolynomiallyBounded tickTime) (hAdapter : PolynomiallyBounded adapterTime)
    (hDivision : PolynomiallyBounded divisionTime) (hTimes : Handler.PolynomialTimes times) :
    PolynomiallyBounded (fun n => Solver.programTime (overhead n) (bound n)
      (inputWidth n) (width n) (outputWidth n) (routeWidth n) (cap n) (basisCap n) (signedCap n)
      (groupCap n) (rowCap n) (coeffCap n) (portWidth n) (fuel n) (tickTime n) (adapterTime n) (divisionTime n) (times n)) := by
  have hHandler := Handler.timeBudget_polynomial overhead width cap basisCap signedCap groupCap rowCap coeffCap portWidth
    times hOverhead hWidth hCap hBasis hSigned hGroups hRows hCoefficients hPort hTimes
  have hTerminal := Solver.terminalTime_polynomial overhead width outputWidth routeWidth cap basisCap signedCap
    adapterTime divisionTime times hOverhead hWidth hOutput hRoute hCap hBasis hSigned hAdapter hDivision hTimes
  have hField := hTimes.fieldTime
  unfold Solver.programTime
  polynomial_bound

theorem Solver.programDescription_polynomial
    (factor caller sampler randomPort handlerPort solverPort fuel allowance instruction : Nat → Nat)
    (hFactor : PolynomiallyBounded factor) (hCaller : PolynomiallyBounded caller)
    (hSampler : PolynomiallyBounded sampler) (hRandom : PolynomiallyBounded randomPort)
    (hHandler : PolynomiallyBounded handlerPort) (hSolver : PolynomiallyBounded solverPort)
    (hFuel : PolynomiallyBounded fuel) (hAllowance : PolynomiallyBounded allowance)
    (hInstruction : PolynomiallyBounded instruction) :
    PolynomiallyBounded (fun n => factor n * Solver.programDescription (caller n) (sampler n)
      (randomPort n) (handlerPort n) (solverPort n) (fuel n) (allowance n) (instruction n)) := by
  dsimp only [Solver.programDescription]
  polynomial_bound

end Signatures.Runtime.SchnorrAGM.Native
