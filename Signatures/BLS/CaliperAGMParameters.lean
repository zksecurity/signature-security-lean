import Signatures.Runtime.Caliper.BLSFullSecurity
import Signatures.BLS.QueryAllowance

/-! Caliper parameters for the public BLS AGM theorem. Layouts, implemented
primitives, sampler and numeric caller allowances are fixed before the attacker.
An attacker supplies actual local Caliper code and its own correspondence and
resource proofs. No completed reduction or backend-adequacy contract is a field.
The source game uses the shared AGM library; these records describe its bounded
Caliper realizations, not a universal conventional-machine coverage theorem. -/
namespace BLS.CaliperAGM
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

abbrev scalarTy : Ty Bool := .atom true
abbrev messageTy : Ty Bool := .atom false
abbrev base (F M : Type) : Bool → Type | true => F | false => M
inductive Comparison : Ty Bool → Ty Bool → Type
  | equal : Comparison (.pair messageTy messageTy) .bool

def primitives (F M : Type) [DecidableEq M] : Primitives (base F M) Comparison where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
def comparison : Expr Comparison [messageTy, messageTy] .bool :=
  .op .equal (.pair (.var .here) (.var (.there .here)))
theorem comparison_correct (F M : Type) [DecidableEq M] (left right : M) :
    comparison.denote (primitives F M) (left, right, ()) = decide (left = right) := rfl

variable (F G K M : Type) [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] [AddCommGroup K] [Module F K] [DecidableEq M]
    (queries : QueryAllowance) (generator : G) (keyGenerator : K)

structure Parameters where
  wordBits : Nat
  State : Type
  layout : BLSFull.Layouts wordBits M F G K State
  routines : BLSFull.Routines layout
  primitiveBounds : BLSFull.Routines.Bounds layout routines
  callerLimits : BLSFull.Caller.Limits
  sampler : Interactive.Code wordBits
  scalarSource : ProbComp layout.scheme.cache.value.Value
  samplerCorrect : Interactive.Refines layout.port .unit layout.scheme.cache.lookup.unit.representation
    layout.scheme.cache.value.representation (fun _ => scalarSource) sampler
  scalarLaw : Subtype.val <$> scalarSource = ($ᵗ F : ProbComp F)
  samplerBudget : BLSFull.Budget
  samplerTime : Interactive.TimeBound layout.port .unit layout.scheme.cache.lookup.unit.representation sampler samplerBudget.time
  samplerWords : (sampler.lower layout.port).descriptionWords ≤ samplerBudget.words
  samplerSlots : Nat
  samplerNames : WordIO.NamesBound (sampler.lower layout.port) samplerSlots
  samplerFits : (sampler.lower layout.port).DescriptionFits
  addresses : BLSFull.AddressBounds (base := base F M) (key := messageTy) (val := scalarTy)
    layout routines primitiveBounds samplerSlots samplerBudget.words
  logRoom : queries.total ≤ layout.tokens.capacity
  cacheRoom : 2 * queries.total + 1 ≤ layout.scheme.cache.capacityPred + 1
  generatorValid : layout.scheme.point.valid generator
  keyGeneratorValid : layout.key.valid keyGenerator

variable {F G K M queries generator keyGenerator}
    (P : Parameters F G K M queries generator keyGenerator)

structure AlgebraicAdversary where
  source : Model.DirectAGM.Adversary F M M G K
  caller : BLSFull.Caller P.layout
  invariant : BLSFull.Caller.Invariant P.layout caller queries.total
  correspondence : BLSFull.Caller.Correspondence P.layout caller invariant
  source_eq : ∀ pk : P.layout.key.Value,
    (fun answer => BLSFull.output answer.val) <$> correspondence.source pk.val =
      (Model.DirectAGM.ProofView.adversary generator source).main pk.val
  localTime : ∀ value, caller.continuation.time value ≤ P.callerLimits.step.time
  initialTime : ∀ value, caller.initialCode.time value ≤ P.callerLimits.initial.time
  localWords : descriptionWords caller.continuation.code ≤ P.callerLimits.step.words
  initialWords : descriptionWords caller.initialCode.code ≤ P.callerLimits.initial.words
  localNames : NamesAccounted caller.continuation.code P.callerLimits.names
  initialNames : NamesAccounted caller.initialCode.code P.callerLimits.names
  randomQueries : ∀ pk, IsQueryBoundP (source.main (Model.LazyAGM.Interactive.initialInput generator pk))
    (fun i => queryKind i.value.data = 0) queries.random
  hashQueries : ∀ pk, IsQueryBoundP (source.main (Model.LazyAGM.Interactive.initialInput generator pk))
    (fun i => queryKind i.value.data = 1) queries.hash
  signingQueries : ∀ pk, IsQueryBoundP (source.main (Model.LazyAGM.Interactive.initialInput generator pk))
    (fun i => queryKind i.value.data = 2) queries.sign

def AlgebraicAdversary.bounds (A : AlgebraicAdversary P) : BLSFull.Caller.Bounds P.layout A.caller where
  step := P.callerLimits.step
  initial := P.callerLimits.initial
  localTime := A.localTime
  initialTime := A.initialTime
  localWords := A.localWords
  initialWords := A.initialWords
  names := P.callerLimits.names
  localNames := A.localNames
  initialNames := A.initialNames

def AlgebraicAdversary.proofView (A : AlgebraicAdversary P) := Model.DirectAGM.ProofView.adversary generator A.source

namespace Parameters
def goodTime : Nat := BLSFull.goodTimeLimit (base := base F M) (key := messageTy) (val := scalarTy)
  P.layout P.routines P.primitiveBounds P.callerLimits P.samplerBudget.time queries.total
def badTime : Nat := BLSFull.badTimeLimit (base := base F M) (key := messageTy) (val := scalarTy)
  P.layout P.routines P.primitiveBounds P.callerLimits P.samplerBudget.time queries.total
def goodWords : Nat := BLSFull.goodWordsLimit (base := base F M) (key := messageTy) (val := scalarTy)
  P.layout P.routines P.primitiveBounds P.callerLimits P.samplerBudget.words queries.total
def badWords : Nat := BLSFull.badWordsLimit (base := base F M) (key := messageTy) (val := scalarTy)
  P.layout P.routines P.primitiveBounds P.callerLimits P.samplerBudget.words queries.total
def names : Nat := max (BLSExtractor.nameBudget P.samplerSlots P.routines.slots) P.callerLimits.names
def goodMemory : Nat := 5 * P.goodWords + 4 * P.names + 3 + P.layout.setup.challenge.representation.encoding.words + P.goodTime
def badMemory : Nat := 5 * P.badWords + 4 * P.names + 3 + P.layout.setup.challenge.representation.encoding.words + P.badTime
def solverCode : Nat := max P.goodWords P.badWords
def solverMemory : Nat := max P.goodMemory P.badMemory

def within (time : Nat) (solver : AlgebraicGroupModel.DLog11Adversary F G K) : Prop :=
  dlogWithin P.layout.port P.layout.setup.challenge P.layout.scheme.cache.value generator keyGenerator P.solverCode P.solverMemory time solver
noncomputable def dlogBound (time : Nat) : ENNReal :=
  dlogSuccessBound P.layout.port P.layout.setup.challenge P.layout.scheme.cache.value generator keyGenerator P.solverCode P.solverMemory time
end Parameters
end BLS.CaliperAGM
