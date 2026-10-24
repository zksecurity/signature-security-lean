import Proofs.Runtime.BackendCoronSolverBudget
import Proofs.Runtime.PolynomialResources

/-! Polynomial closure of the derived native Coron budget. All resource and
encoding caps must be bounded by fixed polynomials in the security parameter;
structural overhead is jointly polynomial in that parameter and frame size.
This certifies the numerical overhead, without asserting backend adequacy or
choosing a uniform/nonuniform cryptographic family. -/

namespace Signatures.Runtime.Coron.NativeSolver

theorem nativeSolverTime_polynomial
    (overhead : Nat → Nat → Nat)
    (inputWidth width routeWidth cap fuel localTime tickTime : Nat → Nat)
    (queries : Fin 3 → Nat → Nat)
    (comparisonTime scalarTime coinTime opTime handlerAdapterTime solverAdapterTime dynamicTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead)
    (hInput : PolynomiallyBounded inputWidth) (hWidth : PolynomiallyBounded width)
    (hRoute : PolynomiallyBounded routeWidth) (hCap : PolynomiallyBounded cap)
    (hFuel : PolynomiallyBounded fuel) (hLocal : PolynomiallyBounded localTime)
    (hTick : PolynomiallyBounded tickTime) (hQueries : ∀ k, PolynomiallyBounded (queries k))
    (hCompare : PolynomiallyBounded comparisonTime) (hScalar : PolynomiallyBounded scalarTime)
    (hCoin : PolynomiallyBounded coinTime) (hOp : PolynomiallyBounded opTime)
    (hHandler : PolynomiallyBounded handlerAdapterTime) (hSolver : PolynomiallyBounded solverAdapterTime)
    (hDynamic : PolynomiallyBounded dynamicTime) :
    PolynomiallyBounded (fun n => nativeSolverTime (overhead n) (inputWidth n) (width n) (routeWidth n)
      (cap n) (fuel n) (localTime n) (tickTime n) (fun k => queries k n) (comparisonTime n)
      (scalarTime n) (coinTime n) (opTime n) (handlerAdapterTime n) (solverAdapterTime n) (dynamicTime n)) := by
  have hReply : PolynomiallyBounded (fun n => nativeReplyTime (overhead n) (width n) (cap n)
      (comparisonTime n) (scalarTime n) (coinTime n) (opTime n)) := by
    dsimp only [nativeReplyTime, ReplyCompiler.replyFrameWidth]
    solve_by_elim (maxDepth := 60) [PolynomiallyBounded.add, PolynomiallyBounded.mul,
      PolynomiallyBounded.const, PolynomialOverhead.apply]
  have hHandlerTime : PolynomiallyBounded (fun n => NativeHandler.nativeHandlerTime (overhead n)
      (width n) (cap n) (comparisonTime n) (scalarTime n) (coinTime n) (opTime n)
      (handlerAdapterTime n) (dynamicTime n)) := by
    dsimp only [NativeHandler.nativeHandlerTime, ReplyCompiler.writtenStoreWidth]
    solve_by_elim (maxDepth := 60) [PolynomiallyBounded.add, PolynomiallyBounded.mul,
      PolynomiallyBounded.const, PolynomialOverhead.apply]
  have hFinish : PolynomiallyBounded (fun n => FinishCompiler.nativeFinishTime (overhead n)
      (width n) (cap n) (comparisonTime n) (scalarTime n) (coinTime n) (opTime n)) := by
    dsimp only [FinishCompiler.nativeFinishTime, FinishCompiler.finishFrameWidth, ReplyCompiler.writtenStoreWidth]
    solve_by_elim (maxDepth := 60) [PolynomiallyBounded.add, PolynomiallyBounded.mul,
      PolynomiallyBounded.const, PolynomialOverhead.apply]
  have hCalls := PolynomiallyBounded.sum
    (fun k n => queries k n * NativeHandler.nativeHandlerTime (overhead n) (width n) (cap n)
      (comparisonTime n) (scalarTime n) (coinTime n) (opTime n) (handlerAdapterTime n) (dynamicTime n))
    (fun k => (hQueries k).mul hHandlerTime)
  dsimp only [nativeSolverTime, ReplyCompiler.writtenStoreWidth]
  solve_by_elim (maxDepth := 100) [PolynomiallyBounded.add, PolynomiallyBounded.mul,
    PolynomiallyBounded.const, PolynomialOverhead.apply]

/-- Polynomial code bounds apply to the actual caller and component descriptions,
including both stored head copies and the numerical loop cap. -/
theorem description_polynomial
    (factor init head update fuel scalarSampler coinSampler dynamicSampler structural instruction handlerPort solverPort : Nat → Nat)
    (hFactor : PolynomiallyBounded factor) (hInit : PolynomiallyBounded init)
    (hHead : PolynomiallyBounded head) (hUpdate : PolynomiallyBounded update)
    (hFuel : PolynomiallyBounded fuel) (hScalar : PolynomiallyBounded scalarSampler)
    (hCoin : PolynomiallyBounded coinSampler) (hDynamic : PolynomiallyBounded dynamicSampler)
    (hStructural : PolynomiallyBounded structural) (hInstruction : PolynomiallyBounded instruction)
    (hHandlerPort : PolynomiallyBounded handlerPort) (hSolverPort : PolynomiallyBounded solverPort) :
    PolynomiallyBounded (fun n => factor n * (init n + 2 * head n + update n + fuel n +
      3 * scalarSampler n + 3 * coinSampler n + dynamicSampler n + 4000 * structural n +
      40 * instruction n + 4 * handlerPort n + 3 * solverPort n + 500)) := by
  have h1 := hInit.add ((PolynomiallyBounded.const 2).mul hHead)
  have h2 := (h1.add hUpdate).add hFuel
  have h3 := h2.add ((PolynomiallyBounded.const 3).mul hScalar)
  have h4 := (h3.add ((PolynomiallyBounded.const 3).mul hCoin)).add hDynamic
  have h5 := h4.add ((PolynomiallyBounded.const 4000).mul hStructural)
  have h6 := h5.add ((PolynomiallyBounded.const 40).mul hInstruction)
  have h7 := h6.add ((PolynomiallyBounded.const 4).mul hHandlerPort)
  have h8 := h7.add ((PolynomiallyBounded.const 3).mul hSolverPort)
  exact hFactor.mul (h8.add (PolynomiallyBounded.const 500))

end Signatures.Runtime.Coron.NativeSolver
