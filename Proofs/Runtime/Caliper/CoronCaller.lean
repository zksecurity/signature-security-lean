import Proofs.Runtime.Caliper.CoronCallerLayout

/-! Constructed co-CDH caller/controller followed by terminal extraction.
Every supported caller exit is ready for the final read by the proved cache
growth bound. There is no supplied implementation of the complete controller. -/
namespace Signatures.Runtime.CaliperBackend.CoronCaller
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G A U : Type}
    [DecidableEq M] [SampleableType F] [SMul F G] [Add G] [Zero G] [Sub G]
    (service : CoronService.Layouts w M F G randomBound qS) (layout : Layouts service A U)
    (default : service.cache.value.Value) (routines : CoronService.Routines service)
    (sampler : CoronService.Sampler service) (arithmetic : CoronTerminal.Arithmetic service)
    (caller : Caller layout) (fuel : Nat) (fallback : service.point.Value)

def controller : Interactive.Code w :=
  BLSCaller.program (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    service.service (service.pairDefault default) randomBound service.randomFits
    (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
    (routines.response service) (routines.response_buffers service) (routines.response_reserve service)
    (sampler.pairCode service) caller.advance layout.state (CoronTerminalFrame.forgery service).representation
    layout.callerFits caller.continuation caller.localNameFits layout.input caller.initial caller.initialCode
    caller.initialNameFits layout.inputFits fuel
def code : Interactive.Code w := .seq (controller service layout default routines sampler caller fuel)
  (CoronCallerFinish.code service layout.pending layout.exitFits default sampler arithmetic fallback)
def called (value : U × service.service.store.Value) : ProbComp layout.Packet :=
  CallerControl.start caller.advance (CoronService.denote service default routines sampler) fuel (caller.initial value.1, value.2)
def denote (value : U × service.service.store.Value) : ProbComp service.point.Value :=
  called service layout default routines sampler caller fuel value >>=
    CoronCallerFinish.denote service default sampler arithmetic fallback

omit [Sub G] in
theorem called_postcondition (value : U × service.service.store.Value) (valid : layout.ready fuel value)
    (answer : layout.Packet) (reached : answer ∈ support (called service layout default routines sampler caller fuel value)) :
    BLSCaller.Postcondition service.service fuel value.2 answer.2 :=
  BLSCaller.start_postcondition (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    service.service (service.pairDefault default) randomBound
    (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
    (routines.response service) (routines.response_buffers service) (routines.response_reserve service)
    (sampler.pairSource service) (sampler.pair_law service) caller.advance fuel (caller.initial value.1, value.2)
    (layout.reserved valid) answer reached
omit [Sub G] in
theorem called_ready (value : U × service.service.store.Value) (valid : layout.ready fuel value)
    (answer : layout.Packet) (reached : answer ∈ support (called service layout default routines sampler caller fuel value)) :
    CoronCallerFinish.ready service default answer :=
  CoronCallerFinish.ready_of_postcondition service default
    (called_postcondition service layout default routines sampler caller fuel value valid answer reached) valid.1 answer.1

variable (invariant : Caller.Invariant layout caller fuel)
include invariant
omit [Sub G] in
theorem controller_refines : Interactive.RefinesOn (layout.ready fuel) service.port .unit layout.incoming
    (CallerStep.output layout.control) (called service layout default routines sampler caller fuel)
    (controller service layout default routines sampler caller fuel) :=
  BLSCaller.refines (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
    service.service (service.pairDefault default) randomBound service.randomFits
    (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
    (routines.response service) (routines.response_buffers service) (routines.response_reserve service)
    (sampler.pairCode service) (sampler.pairSource service) (sampler.pair_correct service) (sampler.pair_law service)
    invariant.domain caller.advance invariant.advance layout.state (CoronTerminalFrame.forgery service).representation
    layout.callerFits caller.continuation caller.localNameFits layout.input caller.initial caller.initialCode
    caller.initialNameFits layout.inputFits fuel (layout.ready fuel) (fun value _ => invariant.initial value.1)
    (fun _ valid => layout.reserved valid)

theorem refines : Interactive.RefinesOn (layout.ready fuel) service.port .unit layout.incoming service.point.representation
    (denote service layout default routines sampler arithmetic caller fuel fallback)
    (code service layout default routines sampler arithmetic caller fuel fallback) := by
  have finished := CoronCallerFinish.refines service layout.pending layout.exitFits default sampler arithmetic fallback
  rw [layout.finish_input] at finished
  exact (controller_refines service layout default routines sampler caller fuel invariant).seq finished
    (called_ready service layout default routines sampler caller fuel)

end Signatures.Runtime.CaliperBackend.CoronCaller
