import Signatures.Runtime.Caliper.CoronFullCoCDH
import Signatures.Runtime.Caliper.CoronFullLimits
import Signatures.BLS.QueryAllowance

/-! Fixed Caliper components and caller allowances for BLS co-CDH security.
An attacker returns an ordinary forgery and supplies local code, termination,
source correspondence and query bounds. The complete reduction's code, time
and total memory are derived, not supplied as implementation assumptions. -/
namespace BLS.CaliperCoCDH
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
variable (F G K M : Type) [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] [AddCommGroup K] [Module F K] [DecidableEq M]
    (queries : QueryAllowance) (generator : G) (keyGenerator : K)

structure Parameters where
  wordBits : Nat
  randomBound : Nat
  signingRange : queries.sign ≤ randomBound
  service : CoronService.Layouts wordBits M F G randomBound ⟨queries.sign, Nat.lt_succ_of_le signingRange⟩
  key : Layout wordBits K
  State : Type
  layout : CoronCaller.Layouts service State key.Value
  input_eq : layout.input = key.representation
  routines : CoronService.Routines service
  sampler : CoronService.Sampler service
  arithmetic : CoronTerminal.Arithmetic service
  scalarKeyFits : service.cache.value.representation.encoding.words + key.representation.encoding.words < 2 ^ wordBits
  keyScale : Implementation .unit (service.cache.value.prod key scalarKeyFits) key (fun value => value.1 • value.2)
  callerLimits : CoronCaller.Caller.Limits
  addresses : CoronCaller.addressBound service routines sampler
  cacheRoom : queries.total + 1 ≤ service.service.cache.capacityPred + 1
  logRoom : queries.total ≤ service.service.capacityPred + 1
  generatorValid : service.point.valid generator
  keyGeneratorValid : key.valid keyGenerator

variable {F G K M queries generator keyGenerator}
    (P : Parameters F G K M queries generator keyGenerator)

namespace Parameters
omit [DecidableEq M] in
theorem challengeFits : P.key.representation.encoding.words + P.service.service.config.representation.encoding.words < 2 ^ P.wordBits := by
  rw [← P.input_eq]
  exact (BLSInitialization.input P.service.service P.layout.input P.layout.inputFits).fits
def challenge := CoronFull.sourceChallenge P.service P.key P.challengeFits
def defaultScalar : P.service.cache.value.Value := ⟨0, CoronFull.scalar_valid P.service P.sampler 0⟩
def fallback : P.service.point.Value := ⟨0, P.routines.zeroValid⟩
def solverTime : Nat := CoronFull.timeLimit P.service P.layout P.routines P.sampler P.arithmetic P.callerLimits queries.total
def solverCode : Nat := CoronFull.codeLimit P.service P.layout P.routines P.sampler P.arithmetic P.callerLimits queries.total
def names : Nat := CoronFull.nameLimit P.service P.routines P.sampler P.arithmetic P.callerLimits
def solverMemory : Nat := CoronFull.memoryLimit P.service P.layout P.routines P.sampler P.arithmetic P.callerLimits queries.total
def within (time : Nat) (solver : CoCDH.CoCDHAdversary F G K) : Prop :=
  coCDHWithin (F := F) P.service.port P.challenge P.service.point generator keyGenerator P.solverCode P.solverMemory time solver

noncomputable def coCDHBound [SampleableType G] (time : Nat) : ENNReal :=
  coCDHSuccessBound (F := F) P.service.port P.challenge P.service.point generator keyGenerator P.solverCode P.solverMemory time
end Parameters

structure Adversary where
  source : ROM.AdversaryPK M G K
  caller : CoronCaller.Caller P.layout
  invariant : CoronCaller.Caller.Invariant P.layout caller queries.total
  correspondence : CoronCaller.Caller.Correspondence P.layout caller invariant K
  inputView : ∀ pk, correspondence.inputView pk = pk.val
  source_eq : ∀ pk : P.key.Value, Subtype.val <$> correspondence.source pk.val = source pk.val
  localTime : ∀ value, caller.continuation.time value ≤ P.callerLimits.stepTime
  initialTime : ∀ value, caller.initialCode.time value ≤ P.callerLimits.initialTime
  localWords : descriptionWords caller.continuation.code ≤ P.callerLimits.stepWords
  initialWords : descriptionWords caller.initialCode.code ≤ P.callerLimits.initialWords
  localNames : NamesAccounted caller.continuation.code P.callerLimits.slots
  initialNames : NamesAccounted caller.initialCode.code P.callerLimits.slots
  randomQueries : ∀ pk, IsQueryBoundP (source pk) (fun i => queryKind i = 0) queries.random
  hashQueries : ∀ pk, IsQueryBoundP (source pk) (fun i => queryKind i = 1) queries.hash
  signingQueries : ∀ pk, IsQueryBoundP (source pk) (fun i => Sum.isRight i = true) queries.sign

def Adversary.bounds (A : Adversary P) : CoronCaller.Caller.Bounds P.layout A.caller where
  stepTime := P.callerLimits.stepTime
  stepWords := P.callerLimits.stepWords
  initialTime := P.callerLimits.initialTime
  initialWords := P.callerLimits.initialWords
  slots := P.callerLimits.slots
  step_time := A.localTime
  step_words := A.localWords
  initial_time := A.initialTime
  initial_words := A.initialWords
  step_names := A.localNames
  initial_names := A.initialNames

end BLS.CaliperCoCDH
