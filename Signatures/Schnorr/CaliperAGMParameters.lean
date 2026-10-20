import Signatures.Runtime.Caliper.SchnorrAGMFullSecurity
import Signatures.Schnorr.QueryAllowance

/-! Fixed Caliper components and local attacker allowances for Schnorr AGM.
The source adversary uses the shared AGM interface. Its implementation supplies
local code, query bounds and correspondence; the complete reduction and all
its resource bounds are constructed from these components. -/
namespace Schnorr.CaliperAGM
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
open Signatures.Runtime.SchnorrAGM.Native

def randomRequest {F G M : Type} (q : Interface.SourceRequest F G M) : Bool :=
  match q.value.data with | .random _ => true | _ => false

variable (F G M : Type) [Field F] [SampleableType F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M]
    (queries : QueryAllowance) (generator : G)

structure Parameters where
  wordBits : Nat
  State : Type
  randomBound : Nat
  layout : CaliperBackend.SchnorrAGM.CallerExtraction.Layouts wordBits M F G queries.hash queries.sign randomBound State
  routines : CaliperBackend.SchnorrAGM.Full.Routines layout
  primitiveBounds : CaliperBackend.SchnorrAGM.Full.Routines.Bounds layout routines
  callerLimits : CaliperBackend.SchnorrAGM.Full.Caller.Limits
  sampler : Interactive.Code wordBits
  scalarSource : ProbComp layout.service.scheme.scalar.Value
  samplerCorrect : Interactive.Refines layout.service.random.port .unit (PairSampling.input wordBits).representation
    layout.service.scheme.scalar.representation (fun _ => scalarSource) sampler
  scalarLaw : Subtype.val <$> scalarSource = ($ᵗ F : ProbComp F)
  sampleTime : Nat
  sampleWords : Nat
  sampleSlots : Nat
  samplerTime : Interactive.TimeBound layout.service.random.port .unit (PairSampling.input wordBits).representation sampler sampleTime
  samplerWords : (sampler.lower layout.service.random.port).descriptionWords ≤ sampleWords
  samplerNames : WordIO.NamesBound (sampler.lower layout.service.random.port) sampleSlots
  samplerFits : (sampler.lower layout.service.random.port).DescriptionFits
  addresses : CaliperBackend.SchnorrAGM.Full.AddressBounds layout routines primitiveBounds sampleSlots sampleWords
  generatorValid : layout.service.scheme.point.valid generator

variable {F G M queries generator} (P : Parameters F G M queries generator)

structure AlgebraicAdversary where
  source : AGM.Adversary F G M
  caller : CaliperBackend.SchnorrAGM.Full.Caller P.layout
  invariant : CaliperBackend.SchnorrAGM.Full.Caller.Invariant P.layout caller queries.total
  correspondence : CaliperBackend.SchnorrAGM.Full.Caller.Source P.layout caller queries.total invariant
  source_eq : ∀ value, (fun answer => Interface.decodeForgery answer.val) <$>
    correspondence.program (correspondence.inputView value) = source.main (AGM.initial value.val.1 value.val.2)
  bounds : CaliperBackend.SchnorrAGM.Full.Caller.Bounds P.layout caller P.callerLimits
  randomQueries : ∀ pk, IsQueryBoundP (source.main (AGM.initial generator pk))
    (fun q => randomRequest q = true) queries.random
  hashQueries : ∀ pk, IsQueryBoundP (source.main (AGM.initial generator pk))
    (fun q => AGM.Reduction.hashRequest q = true) queries.hash
  signingQueries : ∀ pk, IsQueryBoundP (source.main (AGM.initial generator pk))
    (fun q => AGM.Reduction.signRequest q = true) queries.sign

namespace Parameters
def solverTime : Nat := CaliperBackend.SchnorrAGM.Full.timeBudget P.layout P.routines P.primitiveBounds P.callerLimits P.sampleTime queries.total
def solverCode : Nat := CaliperBackend.SchnorrAGM.Full.codeBudget P.layout P.routines P.primitiveBounds P.callerLimits P.sampleWords queries.total
def solverMemory : Nat := CaliperBackend.SchnorrAGM.Full.memoryBudget P.layout P.routines P.primitiveBounds P.callerLimits
  P.sampleTime P.sampleWords P.sampleSlots queries.total
def within (time : Nat) (solver : DiffieHellman.DLogAdversary F G) : Prop :=
  cyclicDLogWithin P.layout.service.random.port P.layout.service.scheme.config P.layout.service.scheme.scalar generator
    P.solverCode P.solverMemory time solver
noncomputable def dlogBound (time : Nat) : ENNReal :=
  cyclicDLogSuccessBound P.layout.service.random.port P.layout.service.scheme.config P.layout.service.scheme.scalar generator
    P.solverCode P.solverMemory time
end Parameters
end Schnorr.CaliperAGM
