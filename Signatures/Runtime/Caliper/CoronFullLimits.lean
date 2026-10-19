import Signatures.Runtime.Caliper.CoronFullBounds

/-! The same complete Coron budgets expressed using numeric caller allowances.
These can be fixed before a caller is chosen. The final equalities connect them
to the resource certificates derived for each implemented caller. -/
namespace Signatures.Runtime.CaliperBackend
open Caliper BoundedSource OracleComp OracleSpec

structure CoronCaller.Caller.Limits where
  stepTime : Nat
  stepWords : Nat
  initialTime : Nat
  initialWords : Nat
  slots : Nat

variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G A U : Type}
    {service : CoronService.Layouts w M F G randomBound qS} {layout : CoronCaller.Layouts service A U}
    {caller : CoronCaller.Caller layout}

def CoronCaller.Caller.Bounds.limits (bounded : CoronCaller.Caller.Bounds layout caller) : CoronCaller.Caller.Limits :=
  ⟨bounded.stepTime, bounded.stepWords, bounded.initialTime, bounded.initialWords, bounded.slots⟩

/-- Actual local code obeys limits chosen before the caller. -/
structure CoronCaller.Caller.Fits (layout : CoronCaller.Layouts service A U)
    (caller : CoronCaller.Caller layout) (limits : CoronCaller.Caller.Limits) : Prop where
  stepTime : ∀ value, caller.continuation.time value ≤ limits.stepTime
  stepWords : descriptionWords caller.continuation.code ≤ limits.stepWords
  initialTime : ∀ value, caller.initialCode.time value ≤ limits.initialTime
  initialWords : descriptionWords caller.initialCode.code ≤ limits.initialWords
  stepNames : NamesAccounted caller.continuation.code limits.slots
  initialNames : NamesAccounted caller.initialCode.code limits.slots

def CoronCaller.Caller.Fits.bounds {limits : CoronCaller.Caller.Limits}
    (fits : CoronCaller.Caller.Fits layout caller limits) : CoronCaller.Caller.Bounds layout caller where
  stepTime := limits.stepTime
  stepWords := limits.stepWords
  initialTime := limits.initialTime
  initialWords := limits.initialWords
  slots := limits.slots
  step_time := fits.stepTime
  step_words := fits.stepWords
  initial_time := fits.initialTime
  initial_words := fits.initialWords
  step_names := fits.stepNames
  initial_names := fits.initialNames

namespace CoronFull
variable [DecidableEq M] [SampleableType F] [SMul F G] [Add G] [Zero G] [Sub G]
    (service : CoronService.Layouts w M F G randomBound qS) (layout : CoronCaller.Layouts service A U)
    (routines : CoronService.Routines service) (sampler : CoronService.Sampler service)
    (arithmetic : CoronTerminal.Arithmetic service) (limits : CoronCaller.Caller.Limits) (fuel : Nat)

def timeLimit : Nat := 8 * layout.incoming.encoding.words +
  (BLSCaller.timeBudget (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    service.service layout.input.encoding.words (CallerStep.width layout.control) (sampler.pairTime service)
    (routines.responseTime service) limits.stepTime limits.initialTime fuel +
    CoronCallerFinish.timeBudget service layout.pending layout.exitFits sampler arithmetic)
def codeLimit : Nat := 26 * layout.incoming.encoding.words + 16 +
  (BLSCaller.codeBudget (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    service.service layout.input.encoding.words (CallerStep.width layout.control) (sampler.pairWords service)
    (routines.responseWords service) limits.stepWords limits.initialWords fuel +
    CoronCallerFinish.codeBudget service layout.pending layout.exitFits sampler arithmetic + 1)
def nameLimit : Nat := max (max (CoronService.nameBudget service routines sampler)
  (CoronTerminal.nameBudget service sampler arithmetic)) limits.slots
def memoryLimit : Nat := 5 * codeLimit service layout routines sampler arithmetic limits fuel +
  4 * nameLimit service routines sampler arithmetic limits + 3 +
    (challenge service layout).representation.encoding.words + timeLimit service layout routines sampler arithmetic limits fuel

variable (caller : CoronCaller.Caller layout) (bounded : CoronCaller.Caller.Bounds layout caller)
theorem timeBudget_eq_limit : timeBudget service layout routines sampler arithmetic caller bounded fuel =
    timeLimit service layout routines sampler arithmetic bounded.limits fuel := rfl
theorem codeBudget_eq_limit : codeBudget service layout routines sampler arithmetic caller bounded fuel =
    codeLimit service layout routines sampler arithmetic bounded.limits fuel := rfl
theorem memoryBudget_eq_limit : memoryBudget service layout routines sampler arithmetic caller bounded fuel =
    memoryLimit service layout routines sampler arithmetic bounded.limits fuel := rfl

end CoronFull
end Signatures.Runtime.CaliperBackend
