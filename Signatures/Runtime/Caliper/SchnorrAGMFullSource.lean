import Signatures.Runtime.Caliper.SchnorrAGMFullCorrectness

/-! Exact connection to the named finite-list DLog reduction. The stored public
configuration is constant across the original oracle simulation. Local caller
correspondence and its query bound identify the generated execution with the
chosen adversary, including its algebraic output explanations. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerHandler
open OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM.Native
variable {F G M Y : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq M] [DecidableEq G] [SampleableType F]

theorem original_run (g pk : G) (program : OracleComp (Interface.sourceSpec F G M) Y)
    (saved : Signatures.Runtime.SchnorrAGM.State F G M) :
    (simulateQ original program).run ((g, pk), saved) =
      (fun answer => (answer.1, (g, pk), answer.2)) <$>
        (simulateQ (Signatures.Runtime.SchnorrAGM.handler g pk) program).run saved := by
  induction program using OracleComp.inductionOn generalizing saved with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind q next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [original, StateT.run, bind_map_left, map_bind]
    apply bind_congr
    rintro ⟨answer, nextStore⟩
    exact ih answer nextStore
end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerHandler

namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Full
open Caliper BoundedSource OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G A : Type}
    (layout : CallerExtraction.Layouts w M F G qH qS randomBound A)
    [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    (routines : Routines layout) (caller : Caller layout)
    (fuel : Nat) (invariant : Caller.Invariant layout caller fuel)

structure Caller.Source where
  Input : Type
  machine : OracleMachine (Interface.sourceSpec F G M) Input layout.forgery.Value
  inputView : layout.service.scheme.config.Value → Input
  stateView : layout.Request × A → machine.State
  program : Input → OracleComp (Interface.sourceSpec F G M) layout.forgery.Value
  implements : machine.ImplementsWithin program fuel
  advance : ∀ remaining hashes signatures q c, invariant.domain (remaining + 1) hashes signatures (q, c) →
    ∀ next : (Interface.sourceSpec F G M).Range (CallerHandler.query layout.service q) → machine.State,
      machine.view (stateView (q, c)) = .inr ⟨CallerHandler.query layout.service q, next⟩ →
      ∀ represented original, CallerHandler.replyMatches layout.service q represented original →
        CallerMachine.Matches machine (CallerHandler.query layout.service) stateView (caller.advance (c, represented)) (next original)
  initial : ∀ value, CallerMachine.Matches machine (CallerHandler.query layout.service) stateView
    (caller.initial value) (machine.init (inputView value))

variable [SampleableType F] (sampleSource : ProbComp layout.service.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampleSource = ($ᵗ F : ProbComp F))
    (witness : Caller.Source layout caller fuel invariant)
    (adversary : _root_.Schnorr.AGM.Adversary F G M)
    (same : ∀ value, (fun answer => Interface.decodeForgery answer.val) <$> witness.program (witness.inputView value) =
      adversary.main (_root_.Schnorr.AGM.initial value.val.1 value.val.2))

include uniform same in
theorem source_original (value : layout.service.scheme.config.Value) :
    Subtype.val <$> source layout routines caller sampleSource fuel value =
      Signatures.Runtime.SchnorrAGM.dlogReduction adversary value.val.1 value.val.2 := by
  have called := CallerExtraction.denote_source layout routines.handler routines.sub routines.divide routines.subNames.buffers
    sampleSource uniform invariant.domain invariant.allowed caller.advance invariant.advance caller.initial fuel
    (admitted layout routines) (fun argument _ => invariant.initial argument.1) (admitted_reserved layout routines)
    witness.machine witness.stateView witness.inputView witness.advance (fun argument _ => witness.initial argument.1)
    witness.program witness.implements (start layout routines value) rfl
  change Subtype.val <$> source layout routines caller sampleSource fuel value = _ at called
  rw [start_stored, CallerHandler.original_run, bind_map_left] at called
  rw [called, Signatures.Runtime.SchnorrAGM.dlogReduction_finishScalar, ← same value]
  simp only [simulateQ_map, StateT.run_bind, map_bind, bind_map_left]
  rfl

variable (sampler : Interactive.Code w)
    (sampleCorrect : Interactive.Refines layout.service.random.port .unit (PairSampling.input w).representation
      layout.service.scheme.scalar.representation (fun _ => sampleSource) sampler)

include uniform same sampleCorrect in
theorem observe_original (tape : RandomTape w) (value : layout.service.scheme.config.Value)
    (before : State w) (holds : layout.service.scheme.config.representation.Holds value before) :
    (fun finished => Subtype.val <$> Interactive.observe layout.service.scheme.scalar.representation finished) <$>
      (program layout routines caller sampler fuel).execute layout.service.random.port .unit tape before =
        some <$> Signatures.Runtime.SchnorrAGM.dlogReduction adversary value.val.1 value.val.2 := by
  have observed := (refines layout routines caller sampler sampleSource sampleCorrect uniform fuel invariant).observe tape value before holds
  have mapped := congrArg (fun computation => (fun answer => Subtype.val <$> answer) <$> computation) observed
  rw [← source_original layout routines caller fuel invariant sampleSource uniform witness adversary same value]
  exact (PFunctor.FreeM.comp_map _ _ _).trans
    (mapped.trans ((PFunctor.FreeM.comp_map _ _ _).symm.trans (PFunctor.FreeM.comp_map some Subtype.val _)))

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Full
