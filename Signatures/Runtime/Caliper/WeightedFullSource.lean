import Signatures.Runtime.Caliper.WeightedFullProgram

/-! Source correspondence for complete initialized weighted programs. The
caller witness describes local machine steps and termination, while the
constructed setup, handler and extractor supply the whole reduction identity. -/
namespace Signatures.Runtime.CaliperBackend.WeightedFull
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM

variable {w : Nat} {C G F M A PK J : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [DecidableEq J]
    (layout : WeightedCallerExtraction.Layouts w (key.Value base) M G F (val.Value base) C A)
    (setup : WeightedSetup.Layouts layout.service PK)
    (caller : Caller layout setup.key.representation) (fuel : Nat)
    (invariant : Invariant layout setup caller fuel) (keys : J ≃ key.Value base)

structure Correspondence where
  source : PK → OracleComp (advSpec J M G) layout.forgery.Value
  machine : OracleMachine (advSpec J M G) PK layout.forgery.Value
  implements : machine.ImplementsWithin source fuel
  stateView : layout.Request × A → machine.State
  advanceMatches : ∀ remaining q c, invariant.domain (remaining + 1) (q, c) →
    ∀ next : (advSpec J M G).Range (WeightedCallerHandler.queryIn layout.service layout.randomBound keys.symm q) → machine.State,
      machine.view (stateView (q, c)) = .inr ⟨WeightedCallerHandler.queryIn layout.service layout.randomBound keys.symm q, next⟩ →
      ∀ represented original, WeightedCallerHandler.replyMatchesIn layout.service layout.randomBound keys.symm q represented original →
        CallerMachine.Matches machine (WeightedCallerHandler.queryIn layout.service layout.randomBound keys.symm) stateView
          (caller.advance (c, represented)) (next original)
  initialMatches : ∀ value : setup.key.Value,
    CallerMachine.Matches machine (WeightedCallerHandler.queryIn layout.service layout.randomBound keys.symm) stateView
      (caller.initial value) (machine.init value.val)

variable [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [Semiring F] [Module F (val.Value base)]
    (routines : Routines layout)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (hashes : Bool) (source : ProbComp layout.service.evaluation.cache.value.Value)
    (coefficientLaw : routines.coefficientDefault.val = 0)
    (combineLaw : ∀ value, routines.combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : layout.zero.val = 0)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (cacheRoom : max 1 layout.terms * (2 * fuel + 1) ≤ layout.service.evaluation.cache.capacityPred + 1)
    (hashRoom : fuel ≤ layout.service.hashCapacityPred + 1)
    (signRoom : fuel ≤ layout.service.signCapacityPred + 1)
    (terms : M → List (J × F))
    (termsEqual : ∀ message, routines.generate message = (terms message).map (Prod.map keys id))
    (witness : Correspondence layout setup caller fuel invariant keys)

include coefficientLaw combineLaw zeroLaw uniform cacheRoom hashRoom signRoom termsEqual in
theorem denote_source (value : setup.challenge.Value) :
    Subtype.val <$> denote layout setup routines P comparison correct caller fuel hashes source value =
      ((simulateQ (WeightedCallerHandler.original terms routines.respond) (witness.source value.val.2.2)).run (value.val.1, [], [], []) >>=
        fun answer => Prod.fst <$> WeightedCallerProgram.extractionSource hashes terms routines.numerator routines.calculate
          (answer.1.val, answer.2.2)) := by
  exact WeightedCallerProgram.denote_equiv layout routines.generator P comparison correct
    routines.update routines.updateNames.buffers (by have := routines.reserve; omega) routines.response
    caller.advance caller.initial fuel routines.coefficientDefault hashes
    routines.extract routines.extractNames.buffers (by have := routines.reserve; omega) routines.sum source
    coefficientLaw combineLaw zeroLaw uniform invariant.domain invariant.advanceValid
    (empty layout setup) (initial_valid layout setup caller fuel invariant)
    (initial_reserved layout setup fuel cacheRoom hashRoom signRoom) (initial_room layout setup fuel cacheRoom)
    keys terms termsEqual witness.machine witness.stateView Subtype.val witness.advanceMatches
    (fun value _ => witness.initialMatches value.1) witness.source witness.implements (setup.start value) rfl

variable (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines layout.port .unit layout.service.evaluation.cache.lookup.unit.representation
      layout.service.evaluation.cache.value.representation (fun _ => source) draw)

include drawCorrect coefficientLaw combineLaw zeroLaw uniform cacheRoom hashRoom signRoom termsEqual in
theorem observe_source (tape : RandomTape w) (value : setup.challenge.Value) (before : State w)
    (holds : setup.challenge.representation.Holds value before) :
    (fun finished => Subtype.val <$> Interactive.observe layout.extraction.scalar.representation finished) <$>
        (code layout setup routines P comparison correct caller draw fuel hashes).execute layout.port .unit tape before =
      some <$> ((simulateQ (WeightedCallerHandler.original terms routines.respond) (witness.source value.val.2.2)).run (value.val.1, [], [], []) >>=
        fun answer => Prod.fst <$> WeightedCallerProgram.extractionSource hashes terms routines.numerator routines.calculate
          (answer.1.val, answer.2.2)) := by
  have observed := (refines layout setup routines P comparison correct caller draw fuel hashes source invariant
    cacheRoom hashRoom signRoom drawCorrect combineLaw zeroLaw uniform).observe tape value before holds
  have erased := congrArg (fun computation => (fun result => Subtype.val <$> result) <$> computation) observed
  have equality := denote_source layout setup caller fuel invariant keys routines P comparison correct hashes source
    coefficientLaw combineLaw zeroLaw uniform cacheRoom hashRoom signRoom terms termsEqual witness value
  rw [← equality]
  simp only [Functor.map_map] at erased ⊢
  convert erased using 1
  rfl
end Signatures.Runtime.CaliperBackend.WeightedFull
