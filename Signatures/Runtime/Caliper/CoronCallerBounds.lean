import Signatures.Runtime.Caliper.CoronCaller
import Signatures.Runtime.Caliper.CoronServiceBounds

/-! The whole caller/extraction program has derived budgets. Local attacker
steps and cryptographic primitives supply their own costs; every generated
controller, oracle, copy, cutoff and extraction instruction is charged here. -/
namespace Signatures.Runtime.CaliperBackend.CoronCaller
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G A U : Type}
    [DecidableEq M] [SampleableType F] [SMul F G] [Add G] [Zero G] [Sub G]
    (service : CoronService.Layouts w M F G randomBound qS) (layout : Layouts service A U)
    (default : service.cache.value.Value) (routines : CoronService.Routines service)
    (sampler : CoronService.Sampler service) (arithmetic : CoronTerminal.Arithmetic service)
    (caller : Caller layout) (bounded : Caller.Bounds layout caller) (fuel : Nat) (fallback : service.point.Value)

def controllerTime : Nat := BLSCaller.timeBudget (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
  service.service layout.input.encoding.words (CallerStep.width layout.control) (sampler.pairTime service)
  (routines.responseTime service) bounded.stepTime bounded.initialTime fuel
def controllerWords : Nat := BLSCaller.codeBudget (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
  service.service layout.input.encoding.words (CallerStep.width layout.control) (sampler.pairWords service)
  (routines.responseWords service) bounded.stepWords bounded.initialWords fuel
def timeBudget : Nat := controllerTime service layout routines sampler caller bounded fuel +
  CoronCallerFinish.timeBudget service layout.pending layout.exitFits sampler arithmetic
def codeBudget : Nat := controllerWords service layout routines sampler caller bounded fuel +
  CoronCallerFinish.codeBudget service layout.pending layout.exitFits sampler arithmetic + 1
def nameBudget : Nat := max (max (CoronService.nameBudget service routines sampler)
  (CoronTerminal.nameBudget service sampler arithmetic)) bounded.slots
def memoryBudget : Nat := 5 * codeBudget service layout routines sampler arithmetic caller bounded fuel +
  4 * nameBudget service layout routines sampler arithmetic caller bounded + 3 + layout.incoming.encoding.words +
    timeBudget service layout routines sampler arithmetic caller bounded fuel

theorem code_words : ((code service layout default routines sampler arithmetic caller fuel fallback).lower service.port).descriptionWords ≤
    codeBudget service layout routines sampler arithmetic caller bounded fuel := by
  have invoked := BLSCaller.words (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    service.service (service.pairDefault default) randomBound service.randomFits
    (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
    (routines.response service) (routines.response_buffers service) (routines.response_reserve service)
    (sampler.pairCode service) caller.advance layout.state (CoronTerminalFrame.forgery service).representation
    layout.callerFits caller.continuation caller.localNameFits layout.input caller.initial caller.initialCode
    caller.initialNameFits layout.inputFits (sampler.pair_words service) (routines.response_bounded service)
    bounded.step_words bounded.initial_words fuel
  have finished := CoronCallerFinish.code_words service layout.pending layout.exitFits default sampler arithmetic fallback
  change ((controller service layout default routines sampler caller fuel).lower service.port).descriptionWords ≤
    controllerWords service layout routines sampler caller bounded fuel at invoked
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, codeBudget]
  omega

theorem names : WordIO.NamesAccounted ((code service layout default routines sampler arithmetic caller fuel fallback).lower service.port)
    (nameBudget service layout routines sampler arithmetic caller bounded) := by
  have invoked := BLSCaller.names (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    service.service (service.pairDefault default) randomBound service.randomFits
    (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
    (routines.response service) (routines.response_buffers service) (routines.response_reserve service)
    (sampler.pairCode service) caller.advance layout.state (CoronTerminalFrame.forgery service).representation
    layout.callerFits caller.continuation caller.localNameFits layout.input caller.initial caller.initialCode
    caller.initialNameFits layout.inputFits (callerSlots := nameBudget service layout routines sampler arithmetic caller bounded)
    (by unfold nameBudget CoronService.nameBudget; omega) (sampler.pair_names service) (routines.response_names service)
    (by unfold nameBudget CoronService.nameBudget; omega) (by unfold nameBudget CoronService.nameBudget; omega)
    (bounded.step_names.mono (by unfold nameBudget; omega)) (bounded.initial_names.mono (by unfold nameBudget; omega)) fuel
  exact invoked.seq ((CoronCallerFinish.names service layout.pending layout.exitFits default sampler arithmetic fallback).mono
    (by unfold nameBudget; omega))

/-- The retention buffer is chosen beyond the constructed service footprint;
this width condition is numerical, using the proved service ledger. -/
def addressBound : Prop := CoronService.nameBudget service routines sampler + CoronService.codeBudget service routines sampler + 1 < 2 ^ w

theorem descriptionFits (addresses : addressBound service routines sampler) :
    ((code service layout default routines sampler arithmetic caller fuel fallback).lower service.port).DescriptionFits := by
  have savedFit : Interactive.savedBuffer service.port (CoronService.code service default routines sampler) < 2 ^ w := by
    have named := (CoronService.names service default routines sampler).buffers
    have stored := CoronService.code_words service default routines sampler
    change ((CoronService.code service default routines sampler).lower service.port).memBound ≤
      CoronService.nameBudget service routines sampler + ((CoronService.code service default routines sampler).lower service.port).descriptionWords at named
    unfold Interactive.savedBuffer
    unfold addressBound at addresses
    have := service.cache.wordFits
    omega
  have invoked := BLSCaller.descriptionFits (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    service.service (service.pairDefault default) randomBound service.randomFits
    (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
    (routines.response service) (routines.response_buffers service) (routines.response_reserve service)
    (sampler.pairCode service) caller.advance layout.state (CoronTerminalFrame.forgery service).representation
    layout.callerFits caller.continuation caller.localNameFits layout.input caller.initial caller.initialCode
    caller.initialNameFits layout.inputFits (sampler.pair_fits service) (sampler.pair_names service) (sampler.pair_reserve service) savedFit fuel
  exact .seq service.cache.wordFits invoked
    (CoronCallerFinish.descriptionFits service layout.pending layout.exitFits default sampler arithmetic fallback)

variable (invariant : Caller.Invariant layout caller fuel)
include invariant
theorem time_bound : Interactive.TimeBoundOn (layout.ready fuel) service.port .unit layout.incoming
    (code service layout default routines sampler arithmetic caller fuel fallback)
    (timeBudget service layout routines sampler arithmetic caller bounded fuel) := by
  have invoked := BLSCaller.time (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    service.service (service.pairDefault default) randomBound service.randomFits
    (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
    (routines.response service) (routines.response_buffers service) (routines.response_reserve service)
    (sampler.pairCode service) (sampler.pairSource service) (sampler.pair_correct service) (sampler.pair_law service)
    invariant.domain caller.advance invariant.advance layout.state (CoronTerminalFrame.forgery service).representation
    layout.callerFits caller.continuation caller.localNameFits layout.input caller.initial caller.initialCode
    caller.initialNameFits layout.inputFits (sampler.pair_time service) (routines.response_bounded service)
    bounded.step_time bounded.initial_time fuel (layout.ready fuel) (fun value _ => invariant.initial value.1)
    (fun _ valid => layout.reserved valid)
  have finished := CoronCallerFinish.time_bound service layout.pending layout.exitFits default sampler arithmetic fallback
  rw [layout.finish_input] at finished
  exact Interactive.TimeBoundOn.seq (controller_refines service layout default routines sampler caller fuel invariant)
    invoked finished (called_ready service layout default routines sampler caller fuel)

theorem within (addresses : addressBound service routines sampler) :
    Interactive.Within service.port (layout.admitted fuel) service.point
      (codeBudget service layout routines sampler arithmetic caller bounded fuel)
      (memoryBudget service layout routines sampler arithmetic caller bounded fuel)
      (timeBudget service layout routines sampler arithmetic caller bounded fuel)
      (fun value => Subtype.val <$> denote service layout default routines sampler arithmetic caller fuel fallback value.val) :=
  Interactive.within_of_refines_accounted (refines service layout default routines sampler arithmetic caller fuel fallback invariant).restrict
    (time_bound service layout default routines sampler arithmetic caller bounded fuel fallback invariant).restrict
    (code_words service layout default routines sampler arithmetic caller bounded fuel fallback)
    (names service layout default routines sampler arithmetic caller bounded fuel fallback)
    (descriptionFits service layout default routines sampler arithmetic caller fuel fallback addresses)

end Signatures.Runtime.CaliperBackend.CoronCaller
