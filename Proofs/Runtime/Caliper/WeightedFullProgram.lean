import Proofs.Runtime.Caliper.WeightedSetup
import Proofs.Runtime.Caliper.WeightedCallerProgramResources
import Proofs.Runtime.Caliper.WeightedCallerReduction

/-! Weighted reduction programs assembled from local routines and caller code.
Setup, query handling, extraction and cutoff are generated; no completed solver
or extractor is supplied through these records. -/
namespace Signatures.Runtime.CaliperBackend.WeightedFull
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {C G F M A PK : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    (layout : WeightedCallerExtraction.Layouts w (key.Value base) M G F (val.Value base) C A)

structure Routines where
  generate : M → List (key.Value base × F)
  generator : Implementation .unit layout.service.message
    (GeneratedWeighted.terms layout.service.evaluation layout.terms layout.termCountFits layout.termStorageFits) generate
  combine : F × (val.Value base × val.Value base) → val.Value base
  update : Implementation .unit layout.service.evaluation.combine layout.service.evaluation.cache.value combine
  respond : Bool → val.Value base × C → G
  response : (signing : Bool) → Implementation .unit layout.service.responseInput layout.service.point (respond signing)
  calculate : F × (val.Value base × val.Value base) → F
  extract : Implementation .unit layout.service.evaluation.combine layout.extraction.scalar calculate
  numerator : F × val.Value base → F
  sum : Implementation .unit layout.extraction.numeratorInput layout.extraction.scalar numerator
  coefficientDefault : layout.extraction.scalar.Value
  slots : Nat
  reserve : slots + 5 < 2 ^ w
  generatorNames : NamesBound generator.program.code slots
  updateNames : NamesBound update.program.code slots
  responseNames : ∀ signing, NamesBound (response signing).program.code slots
  extractNames : NamesBound extract.program.code slots
  sumNames : NamesBound sum.program.code slots

structure Caller (input : Representation w PK) where
  advance : A × layout.Reply → layout.forgery.Value ⊕ (layout.Request × A)
  continuation : Realizer .unit (CallerStep.resume layout.control) (CallerStep.next layout.control) advance
  localNameFits : continuation.savedBuffer < 2 ^ w
  initial : PK → layout.forgery.Value ⊕ (layout.Request × A)
  initialCode : Realizer .unit input (CallerStep.next layout.control) initial
  initialNameFits : initialCode.savedBuffer < 2 ^ w

variable [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
    (setup : WeightedSetup.Layouts layout.service PK)
    (routines : Routines layout)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (caller : Caller layout setup.key.representation) (draw : Interactive.Code w)
    (fuel : Nat) (hashes : Bool)

def tail : Interactive.Code w :=
  WeightedCallerProgram.code layout routines.generator P comparison correct
    routines.update routines.updateNames.buffers (by have := routines.reserve; omega) draw
    routines.response (fun signing => (routines.responseNames signing).buffers) (by have := routines.reserve; omega)
    caller.advance caller.continuation caller.localNameFits setup.key.representation
    caller.initial caller.initialCode caller.initialNameFits setup.outputFits fuel
    routines.coefficientDefault hashes routines.extract routines.extractNames.buffers (by have := routines.reserve; omega)
    routines.sum routines.sumNames.buffers (by have := routines.reserve; omega)
def code : Interactive.Code w :=
  .seq (.compute (WeightedSetup.realizer setup).code) (tail layout setup routines P comparison correct caller draw fuel hashes)

variable (source : ProbComp layout.service.evaluation.cache.value.Value)
def tailSource : setup.key.Value × layout.service.store.Value → ProbComp layout.extraction.scalar.Value :=
  WeightedCallerProgram.denote layout routines.generator P comparison correct
    routines.update routines.updateNames.buffers (by have := routines.reserve; omega) routines.response
    caller.advance caller.initial fuel routines.coefficientDefault hashes
    routines.extract routines.extractNames.buffers (by have := routines.reserve; omega) routines.sum source
def denote (value : setup.challenge.Value) : ProbComp layout.extraction.scalar.Value :=
  tailSource layout setup routines P comparison correct caller fuel hashes source (setup.start value)

structure Invariant where
  domain : Nat → layout.Request × A → Prop
  advanceValid : ∀ remaining q c, domain (remaining + 1) (q, c) →
    ∀ represented original, WeightedCallerHandler.replyMatches layout.service layout.randomBound q represented original →
      WeightedCaller.HeadValid layout.service layout.randomBound domain remaining (caller.advance (c, represented))
  initialValid : ∀ value, WeightedCaller.HeadValid layout.service layout.randomBound domain fuel (caller.initial value)

variable (invariant : Invariant layout setup caller fuel)
    (cacheRoom : max 1 layout.terms * (2 * fuel + 1) ≤ layout.service.evaluation.cache.capacityPred + 1)
    (hashRoom : fuel ≤ layout.service.hashCapacityPred + 1)
    (signRoom : fuel ≤ layout.service.signCapacityPred + 1)

def empty (value : setup.key.Value × layout.service.store.Value) : Prop := value.2.val.2 = ([], [], [])

omit [DecidableEq (key.Value base)] [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
theorem initial_valid (value : setup.key.Value × layout.service.store.Value) (_valid : empty layout setup value) :
    WeightedCaller.HeadValid layout.service layout.randomBound invariant.domain fuel (caller.initial value.1) :=
  invariant.initialValid value.1
omit [DecidableEq (key.Value base)] [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include cacheRoom hashRoom signRoom in
theorem initial_reserved (value : setup.key.Value × layout.service.store.Value) (valid : empty layout setup value) :
    WeightedOracle.Reserved layout.service layout.terms fuel value.2.val := by
  have reserved := (WeightedInitialization.extraction_reserved layout.service layout.terms fuel cacheRoom hashRoom signRoom
    ⟨value.2.val.1, value.2.property.1⟩).1
  have same : value.2.val = (WeightedInitialization.store layout.service ⟨value.2.val.1, value.2.property.1⟩).val :=
    Prod.ext rfl valid
  rw [same]
  exact reserved
omit [DecidableEq (key.Value base)] [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include cacheRoom in
theorem initial_room (value : setup.key.Value × layout.service.store.Value) (valid : empty layout setup value) :
    value.2.val.2.1.length + max 1 layout.terms *
      (value.2.val.2.2.1.length + value.2.val.2.2.2.length + 2 * fuel + 1) ≤ layout.service.evaluation.cache.capacityPred + 1 := by
  change value.2.val.2 = ([], [], []) at valid
  rw [valid]
  simpa only [List.length_nil, Nat.zero_add] using cacheRoom

variable (drawCorrect : Interactive.Refines layout.port .unit layout.service.evaluation.cache.lookup.unit.representation
      layout.service.evaluation.cache.value.representation (fun _ => source) draw)
    (combineLaw : ∀ value, routines.combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : layout.zero.val = 0)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include drawCorrect combineLaw zeroLaw uniform invariant cacheRoom hashRoom signRoom in
theorem tail_refines : Interactive.RefinesOn (empty layout setup) layout.port .unit setup.callerInput
    layout.extraction.scalar.representation (tailSource layout setup routines P comparison correct caller fuel hashes source)
    (tail layout setup routines P comparison correct caller draw fuel hashes) :=
  WeightedCallerProgram.refines layout routines.generator P comparison correct
    routines.update routines.updateNames.buffers (by have := routines.reserve; omega) draw
    routines.response (fun signing => (routines.responseNames signing).buffers) (by have := routines.reserve; omega)
    caller.advance caller.continuation caller.localNameFits setup.key.representation
    caller.initial caller.initialCode caller.initialNameFits setup.outputFits fuel
    routines.coefficientDefault hashes routines.extract routines.extractNames.buffers (by have := routines.reserve; omega)
    routines.sum routines.sumNames.buffers (by have := routines.reserve; omega)
    source drawCorrect combineLaw zeroLaw uniform invariant.domain invariant.advanceValid (empty layout setup)
    (initial_valid layout setup caller fuel invariant) (initial_reserved layout setup fuel cacheRoom hashRoom signRoom)
    (initial_room layout setup fuel cacheRoom)

include drawCorrect combineLaw zeroLaw uniform invariant cacheRoom hashRoom signRoom in
theorem refines : Interactive.Refines layout.port .unit setup.challenge.representation layout.extraction.scalar.representation
    (denote layout setup routines P comparison correct caller fuel hashes source)
    (code layout setup routines P comparison correct caller draw fuel hashes) := by
  have prepared := Interactive.Refines.compute layout.port .unit (WeightedSetup.realizer setup)
  have tail := tail_refines layout setup routines P comparison correct caller draw fuel hashes source invariant
    cacheRoom hashRoom signRoom drawCorrect combineLaw zeroLaw uniform
  have joined := (prepared.on (fun _ => True)).seq tail (by
    intro value _ answer supported
    have same : answer = setup.start value := by simpa only [support_pure, Set.mem_singleton_iff] using supported
    subst answer
    rfl)
  intro tape value before holds
  simpa only [pure_bind, code, denote] using joined tape value trivial before holds
end Signatures.Runtime.CaliperBackend.WeightedFull
