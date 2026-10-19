import Signatures.Runtime.Caliper.CoronFull

/-! Complete bounds include the executed creation of empty private storage,
initial challenge data, both stored terminal branches and all caller copies. -/
namespace Signatures.Runtime.CaliperBackend.CoronFull
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G A U : Type}
    [DecidableEq M] [SampleableType F] [SMul F G] [Add G] [Zero G] [Sub G]
    (service : CoronService.Layouts w M F G randomBound qS) (layout : CoronCaller.Layouts service A U)
    (default : service.cache.value.Value) (routines : CoronService.Routines service)
    (sampler : CoronService.Sampler service) (arithmetic : CoronTerminal.Arithmetic service)
    (caller : CoronCaller.Caller layout) (bounded : CoronCaller.Caller.Bounds layout caller)
    (fuel : Nat) (fallback : service.point.Value)

def timeBudget : Nat := 8 * layout.incoming.encoding.words +
  CoronCaller.timeBudget service layout routines sampler arithmetic caller bounded fuel
def codeBudget : Nat := 26 * layout.incoming.encoding.words + 16 +
  CoronCaller.codeBudget service layout routines sampler arithmetic caller bounded fuel
def memoryBudget : Nat := 5 * codeBudget service layout routines sampler arithmetic caller bounded fuel +
  4 * CoronCaller.nameBudget service layout routines sampler arithmetic caller bounded + 3 +
  (challenge service layout).representation.encoding.words + timeBudget service layout routines sampler arithmetic caller bounded fuel

theorem code_words : ((code service layout default routines sampler arithmetic caller fuel fallback).lower service.port).descriptionWords ≤
    codeBudget service layout routines sampler arithmetic caller bounded fuel := by
  have initialized := BLSInitialization.words service.service layout.input layout.inputFits
  have called := CoronCaller.code_words service layout default routines sampler arithmetic caller bounded fuel fallback
  change descriptionWords (setup service layout).code ≤ 26 * layout.incoming.encoding.words + 14 at initialized
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute, codeBudget]
  omega
theorem names : WordIO.NamesAccounted ((code service layout default routines sampler arithmetic caller fuel fallback).lower service.port)
    (CoronCaller.nameBudget service layout routines sampler arithmetic caller bounded) :=
  (WordIO.NamesAccounted.compute ((BLSInitialization.names service.service layout.input layout.inputFits).accounted.mono
    (by unfold CoronCaller.nameBudget CoronService.nameBudget; omega))).seq
    (CoronCaller.names service layout default routines sampler arithmetic caller bounded fuel fallback)
theorem descriptionFits (addresses : CoronCaller.addressBound service routines sampler) :
    ((code service layout default routines sampler arithmetic caller fuel fallback).lower service.port).DescriptionFits :=
  .seq service.cache.wordFits (.compute (setup service layout).description_fits)
    (CoronCaller.descriptionFits service layout default routines sampler arithmetic caller fuel fallback addresses)

variable (invariant : CoronCaller.Caller.Invariant layout caller fuel)
    (cacheRoom : fuel + 1 ≤ service.service.cache.capacityPred + 1) (logRoom : fuel ≤ service.service.capacityPred + 1)
include invariant cacheRoom logRoom
theorem time_bound : Interactive.TimeBound service.port .unit (challenge service layout).representation
    (code service layout default routines sampler arithmetic caller fuel fallback)
    (timeBudget service layout routines sampler arithmetic caller bounded fuel) := by
  have initialized := ((Interactive.Refines.compute service.port .unit (setup service layout)).viewInput
    (challenge service layout).representation Subtype.val (fun _ => rfl)).on (fun _ => True)
  have timed := ((Interactive.TimeBound.compute (port := service.port) (cost := .unit) (setup service layout)
    _ (BLSInitialization.time service.service layout.input layout.inputFits)).viewInput
      (challenge service layout).representation Subtype.val (fun _ => rfl)).on (fun _ => True)
  have composed := Interactive.TimeBoundOn.seq initialized timed
    (CoronCaller.time_bound service layout default routines sampler arithmetic caller bounded fuel fallback invariant) (by
      intro value _ answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact start_ready service layout fuel cacheRoom logRoom value)
  exact fun tape value before holds => composed tape value trivial before holds

theorem within (addresses : CoronCaller.addressBound service routines sampler) :
    Interactive.Within service.port (challenge service layout) service.point
      (codeBudget service layout routines sampler arithmetic caller bounded fuel)
      (memoryBudget service layout routines sampler arithmetic caller bounded fuel)
      (timeBudget service layout routines sampler arithmetic caller bounded fuel)
      (fun value => Subtype.val <$> denote service layout default routines sampler arithmetic caller fuel fallback value) :=
  Interactive.within_of_refines_accounted
    (refines service layout default routines sampler arithmetic caller fuel fallback invariant cacheRoom logRoom)
    (time_bound service layout default routines sampler arithmetic caller bounded fuel fallback invariant cacheRoom logRoom)
    (code_words service layout default routines sampler arithmetic caller bounded fuel fallback)
    (names service layout default routines sampler arithmetic caller bounded fuel fallback)
    (descriptionFits service layout default routines sampler arithmetic caller fuel fallback addresses)

end Signatures.Runtime.CaliperBackend.CoronFull
