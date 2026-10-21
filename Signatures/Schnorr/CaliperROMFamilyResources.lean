import Signatures.Schnorr.Proofs.CaliperROM
import Signatures.Runtime.Caliper.SchnorrROMHandlerWordsBound
import Signatures.Runtime.Caliper.CyclicDLogFamily
import Signatures.Runtime.Caliper.PolynomialBounds

/-! Polynomial bounds on the fixed ordinary-ROM Caliper components imply
polynomial code, total memory and runtime for the complete replaying solver.
Scalar-domain size is unrestricted; encoded widths, capacities, primitive
budgets and the attacker's declared local allowances are what is bounded. -/
namespace Schnorr.CaliperROM.Family
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
variable {F G M : Nat → Type} [∀ n, Field (F n)] [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
    [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)]
    {queries : Nat → QueryAllowance} {generator : ∀ n, G n}
    (parameters : ∀ n, Parameters (F n) (G n) (M n) (queries n) (generator n))

/-- Component assumptions only; complete-solver resources are conclusions. -/
structure PolynomialResources : Prop where
  queries : PolynomiallyBounded (fun n => (queries n).total)
  wordBits : PolynomiallyBounded (fun n => (parameters n).wordBits)
  messageWidth : PolynomiallyBounded (fun n => (parameters n).config.message.representation.encoding.words)
  pointWidth : PolynomiallyBounded (fun n => (parameters n).config.point.representation.encoding.words)
  stateWidth : PolynomiallyBounded (fun n => (parameters n).shape.state.encoding.words)
  tables : PolynomiallyBounded (fun n => (parameters n).config.capacityPred)
  tapes : PolynomiallyBounded (fun n => (parameters n).config.sampler.capacity)
  primitiveNames : PolynomiallyBounded (fun n => (parameters n).operations.slots)
  arithmeticNames : PolynomiallyBounded (fun n => (parameters n).arithmetic.slots)
  callerNames : PolynomiallyBounded (fun n => (parameters n).limits.names)
  localTime : PolynomiallyBounded (fun n => (parameters n).limits.localTime)
  localWords : PolynomiallyBounded (fun n => (parameters n).limits.localWords)
  initialTime : PolynomiallyBounded (fun n => (parameters n).limits.initialTime)
  initialWords : PolynomiallyBounded (fun n => (parameters n).limits.initialWords)
  scaleTime : PolynomiallyBounded (fun n => (parameters n).handlerBudget.scaleTime)
  scaleWords : PolynomiallyBounded (fun n => (parameters n).handlerBudget.scaleWords)
  pointSubTime : PolynomiallyBounded (fun n => (parameters n).handlerBudget.subTime)
  pointSubWords : PolynomiallyBounded (fun n => (parameters n).handlerBudget.subWords)
  scalarSubTime : PolynomiallyBounded (fun n => (parameters n).arithmeticBudget.subTime)
  scalarSubWords : PolynomiallyBounded (fun n => (parameters n).arithmeticBudget.subWords)
  divideTime : PolynomiallyBounded (fun n => (parameters n).arithmeticBudget.divideTime)
  divideWords : PolynomiallyBounded (fun n => (parameters n).arithmeticBudget.divideWords)

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem copySlice_polynomial {wb f : Nat → Nat} (source destination start : Nat) (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun n => (copySlice (w := wb n) source destination start (f n)).staticTime WordIO.Costs.unit.machine) := by
  simp only [copySlice_staticTime]
  exact hf.mul (PolynomiallyBounded.const _)

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem dispatchTime_polynomial {wb a b c d : Nat → Nat} (ha : PolynomiallyBounded a) (hb : PolynomiallyBounded b)
    (hc : PolynomiallyBounded c) (hd : PolynomiallyBounded d) :
    PolynomiallyBounded (fun n => Interactive.dispatchTime (w := wb n) .unit (a n) (b n) (c n) (d n)) := by
  simp only [Interactive.dispatchTime, selectSlice_staticTime]
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
/-- Tape padding is a remainder of zero; the closure tactic has no remainder rule. -/
theorem padding : PolynomiallyBounded (fun n => 0 % ((parameters n).config.handler.sampler.tape.capacity + 1)) :=
  (PolynomiallyBounded.const 0).of_le (fun n => by simp)

namespace PolynomialResources
variable {parameters} (resources : PolynomialResources parameters)
include resources

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem hashQueries : PolynomiallyBounded (fun n => (queries n).hash) :=
  resources.queries.of_le (fun n => by unfold QueryAllowance.total; omega)
omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem signingQueries : PolynomiallyBounded (fun n => (queries n).sign) :=
  resources.queries.of_le (fun n => by unfold QueryAllowance.total; omega)

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem rawInputWidth : PolynomiallyBounded (fun n => (SchnorrROM.ReplaySecond.rawInput (parameters n).config).encoding.words) := by
  have hashBound := resources.hashQueries
  have padBound := padding parameters
  cases resources
  caliper_polynomial
omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem challengeInputWidth : PolynomiallyBounded (fun n => (SchnorrROM.ReplayChallenge.input (parameters n).config).encoding.words) := by
  have hashBound := resources.hashQueries
  have padBound := padding parameters
  cases resources
  caliper_polynomial
omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem outputWidth : PolynomiallyBounded (fun n => (SchnorrROM.ReplayFork.output (parameters n).config).encoding.words) := by
  have hashBound := resources.hashQueries
  have padBound := padding parameters
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] in
/-- The handler's signing code embeds the enumerated sampler's actual programs;
their constant sizes give a width-only formula. -/
theorem handlerCode : PolynomiallyBounded (fun n =>
    SchnorrROM.Handler.codeBudget (parameters n).config (parameters n).operations (parameters n).handlerBudget) := by
  have bound : PolynomiallyBounded (fun n =>
      SchnorrROM.Handler.codeBudgetBound (parameters n).config (parameters n).operations (parameters n).handlerBudget) := by
    have hashBound := resources.hashQueries
    have padBound := padding parameters
    cases resources
    caliper_polynomial
  exact bound.of_le (fun n => SchnorrROM.Handler.codeBudget_le _ _ _)

omit [∀ n, DecidableEq (F n)] in
theorem replayTime : PolynomiallyBounded (fun n => SchnorrROM.Full.replayTime (parameters n).config (parameters n).shape (parameters n).limits
    (parameters n).operations (parameters n).handlerBudget (queries n).hash (parameters n).indexFits (queries n).total) := by
  have hashBound := resources.hashQueries
  have padBound := padding parameters
  cases resources
  caliper_polynomial
omit [∀ n, DecidableEq (F n)] in
theorem guardTime : PolynomiallyBounded (fun n => SchnorrROM.Full.guardTime (parameters n).config (parameters n).shape (parameters n).limits
    (parameters n).operations (parameters n).handlerBudget (queries n).hash (parameters n).indexFits (queries n).total) := by
  unfold SchnorrROM.Full.guardTime
  exact dispatchTime_polynomial resources.rawInputWidth resources.rawInputWidth resources.replayTime
    ((PolynomiallyBounded.const 8).mul resources.outputWidth)
omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem checkedTime : PolynomiallyBounded (fun n => SchnorrROM.ReplayChallenge.Checked.timeBudget (parameters n).config) := by
  have hashBound := resources.hashQueries
  have padBound := padding parameters
  cases resources
  caliper_polynomial
omit [∀ n, DecidableEq (F n)] in
theorem afterTime : PolynomiallyBounded (fun n => SchnorrROM.Full.afterTime (parameters n).config (parameters n).shape (parameters n).limits
    (parameters n).operations (parameters n).handlerBudget (queries n).hash (parameters n).indexFits (queries n).total) := by
  unfold SchnorrROM.Full.afterTime
  exact resources.checkedTime.add resources.guardTime
omit [∀ n, DecidableEq (F n)] in
theorem branchTime : PolynomiallyBounded (fun n => SchnorrROM.Full.branchTime (parameters n).config (parameters n).shape (parameters n).limits
    (parameters n).operations (parameters n).handlerBudget (queries n).hash (parameters n).indexFits (queries n).total) := by
  unfold SchnorrROM.Full.branchTime
  exact dispatchTime_polynomial resources.challengeInputWidth resources.challengeInputWidth
    ((PolynomiallyBounded.const 8).mul resources.outputWidth) resources.afterTime
omit [∀ n, DecidableEq (F n)] in
theorem firstTime : PolynomiallyBounded (fun n => SchnorrROM.Full.firstTime (parameters n).config (parameters n).shape (parameters n).limits
    (parameters n).operations (parameters n).handlerBudget (queries n).hash (parameters n).indexFits (queries n).total) := by
  have hashBound := resources.hashQueries
  have padBound := padding parameters
  cases resources
  caliper_polynomial
omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem inputWidth : PolynomiallyBounded (fun n => (SchnorrROM.Pass.Initialization.input (parameters n).config).encoding.words) := by
  have hashBound := resources.hashQueries
  have padBound := padding parameters
  cases resources
  caliper_polynomial
omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem extractTime : PolynomiallyBounded (fun n =>
    SchnorrROM.ReplayFork.Extract.timeBudget (parameters n).config (parameters n).arithmetic (parameters n).arithmeticBudget) := by
  have hashBound := resources.hashQueries
  have padBound := padding parameters
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] in
theorem solverTime : PolynomiallyBounded (fun n => (parameters n).solverTime) := by
  unfold Parameters.solverTime SchnorrROM.Full.timeBudget SchnorrROM.Full.initializedTime SchnorrROM.Full.forkTime
  exact ((((PolynomiallyBounded.const 8).mul resources.inputWidth).add
    (resources.firstTime.add resources.branchTime)).add resources.extractTime)

omit [∀ n, DecidableEq (F n)] in
theorem solverCode : PolynomiallyBounded (fun n => (parameters n).solverCode) := by
  have hashBound := resources.hashQueries
  have padBound := padding parameters
  have handler := resources.handlerCode
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem names : PolynomiallyBounded (fun n =>
    SchnorrROM.Full.nameBudget (parameters n).config (parameters n).limits (parameters n).operations (parameters n).arithmetic) := by
  have hashBound := resources.hashQueries
  have padBound := padding parameters
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem pointsWidth : PolynomiallyBounded (fun n => (SchnorrROM.Pass.Initialization.points (parameters n).config).representation.encoding.words) := by
  have hashBound := resources.hashQueries
  have padBound := padding parameters
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] in
theorem solverMemory : PolynomiallyBounded (fun n => (parameters n).solverMemory) := by
  unfold Parameters.solverMemory SchnorrROM.Full.memoryBudget
  exact (((((PolynomiallyBounded.const 5).mul resources.solverCode).add
    ((PolynomiallyBounded.const 4).mul resources.names)).add (PolynomiallyBounded.const 3)).add resources.pointsWidth).add
    resources.solverTime
end PolynomialResources

variable [inst : ∀ n, SampleableType (F n)] [∀ n, SampleableType (G n)]

/-- Hardness in the fixed Caliper family against every polynomial-resource
solver family, not just the particular Schnorr reduction. -/
def dlogHardness : Prop :=
  cyclicDLogNonuniformHardness (fun n => SchnorrROMTape.Fresh.port (parameters n).config.handler.sampler.tape)
    (fun n => SchnorrROM.Pass.Initialization.points (parameters n).config)
    (fun n => (parameters n).config.handler.sampler.tape.scalar) generator

include inst in
theorem reduction_nonuniform (resources : PolynomialResources parameters)
    (adversary : ∀ n, UnrestrictedAdversary (parameters n))
    (sampled : ∀ n, inst n = SchnorrROMTape.PrivateSampler.Enumerated.sampleable (parameters n).config.sampler) :
    cyclicDLogNonuniformWithin (fun n => SchnorrROMTape.Fresh.port (parameters n).config.handler.sampler.tape)
      (fun n => SchnorrROM.Pass.Initialization.points (parameters n).config)
      (fun n => (parameters n).config.handler.sampler.tape.scalar) generator
      (fun n => Schnorr.ListROM.NativeSolver.reduction (G₂ := G n) (K := M n) (adversary n).source.main (queries n).hash) :=
  cyclicDLogNonuniformWithin.of_pointwise _ _ _ _ _
    (fun n => (parameters n).solverCode) (fun n => (parameters n).solverMemory) (fun n => (parameters n).solverTime)
    resources.wordBits resources.solverCode resources.solverMemory resources.solverTime
    (fun n => reduction_within (parameters n) (adversary n) (sampled n))

end Schnorr.CaliperROM.Family
