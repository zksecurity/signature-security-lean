import Signatures.Runtime.Caliper.WeightedCallerProgramSourceEquiv
import Signatures.Runtime.WeightedExtraction

/-! The full caller source and extraction are exactly the existing weighted
AGM reductions, after erasing bounded algebraic-output representations. Cache
and chronological transcript order are retained throughout. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCallerHandler
open OracleComp OracleSpec
variable {K M F R C G Y : Type} [DecidableEq K] [SampleableType R] [AddCommMonoid R] [SMul F R]

theorem original_run (terms : M → List (K × F)) (respond : Bool → R × C → G) (configuration : C)
    (program : OracleComp (Model.LazyAGM.advSpec K M G) Y) (stored : WeightedAGM.State K M R G) :
    (simulateQ (original terms respond) program).run (configuration, stored) =
      (fun answer => (answer.1, configuration, answer.2)) <$>
        (simulateQ (WeightedAGM.listOracle terms (fun sample => respond false (sample, configuration))
          (fun sample => respond true (sample, configuration))) program).run stored := by
  induction program using OracleComp.inductionOn generalizing stored with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind q next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [original, StateT.run, bind_map_left, map_bind]
    apply bind_congr
    rintro ⟨answer, nextStore⟩
    exact ih answer nextStore
end Signatures.Runtime.CaliperBackend.WeightedCallerHandler

namespace Signatures.Runtime.CaliperBackend.WeightedCallerProgram
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction (privateListOracle)

variable {F K M G Y PK : Type}
def output (value : M × (F × (List F × List F))) : Model.LazyAGM.Output F M :=
  ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩

variable [Field F] [SampleableType F] [DecidableEq K] (terms : M → List (K × F))

theorem good_extraction_original (value : ExtractionInput K M G F F) :
    extractionSource true terms (fun value => value.1 + value.2)
      (fun value => value.1 / (value.2.1 - value.2.2)) value =
      (simulateQ privateListOracle
        (WeightedAGM.Extract.goodFinish terms (output value.1) (WeightedAGM.Reply.chronological value.2.2))).run value.2.1 := by
  simp only [extractionSource, ↓reduceIte, WeightedAGM.Extract.goodFinish,
    simulateQ_bind, StateT.run_bind, bind_pure_comp, simulateQ_map, StateT.run_map,
    output, WeightedAGM.Reply.chronological]

theorem bad_extraction_original (numerator : F × (F × F) → F) (value : ExtractionInput K M G F (F × F)) :
    extractionSource false terms numerator
      (fun value => -(value.2.1.2 - value.2.2.2) / (value.2.1.1 - value.2.2.1)) value =
      (simulateQ privateListOracle
        (WeightedAGM.Extract.badFinish terms (output value.1) (WeightedAGM.Reply.chronological value.2.2))).run value.2.1 := by
  simp only [extractionSource, Bool.false_eq_true, ↓reduceIte, WeightedAGM.Extract.badFinish,
    simulateQ_bind, StateT.run_bind, bind_pure_comp, simulateQ_map, StateT.run_map,
    output, WeightedAGM.Reply.chronological]

variable [AddCommGroup G] [Module F G]
    (view : Y → M × (F × (List F × List F)))
    (program : OracleComp (advSpec K M G) Y)
    (adversary : Adversary F K M G PK) (g X : G) (generator pk : PK)
    (same : (fun answer => output (view answer)) <$> program = adversary.main pk)

include same in
theorem good_original_finish :
    ((simulateQ (WeightedCallerHandler.original terms
      (fun signing (sample : F × (G × G)) => sample.1 • (if signing then sample.2.2 else sample.2.1)))
      program).run ((g, X), [], [], []) >>=
        fun answer => Prod.fst <$> extractionSource true terms (fun value => value.1 + value.2)
          (fun value => value.1 / (value.2.1 - value.2.2)) (view answer.1, answer.2.2)) =
      WeightedReduction.goodReductionList terms adversary g X generator pk := by
  have run := WeightedAGM.listRun terms (fun scalar : F => scalar • g) (fun scalar => scalar • X) adversary pk
  rw [← same, simulateQ_map, StateT.run_map, Functor.map_map] at run
  have joined := congrArg
    (fun computation : ProbComp ((Output F M × Transcript K M G) × List (K × F)) =>
      computation >>= fun answer => Prod.fst <$>
        (simulateQ privateListOracle (WeightedAGM.Extract.goodFinish terms answer.1.1 answer.1.2)).run answer.2) run
  rw [WeightedCallerHandler.original_run, bind_map_left]
  change _ = Prod.fst <$> (simulateQ privateListOracle (WeightedReduction.goodProgram terms g X pk adversary)).run []
  rw [WeightedAGM.Extract.goodProgram_finish, simulateQ_bind, StateT.run_bind, map_bind]
  simpa only [WeightedAGM.observe, bind_map_left, good_extraction_original, output,
    Function.comp_apply, Bool.false_eq_true, ite_false, ite_true] using joined

include same in
theorem bad_original_finish (scalar : F) (numerator : F × (F × F) → F) :
    ((simulateQ (WeightedCallerHandler.original terms
      (fun signing (sample : (F × F) × (F × (G × G))) =>
        if signing then sample.2.1 • (sample.1.1 • sample.2.2.2 + sample.1.2 • sample.2.2.1)
        else sample.1.1 • sample.2.2.2 + sample.1.2 • sample.2.2.1))
      program).run ((scalar, g, X), [], [], []) >>=
        fun answer => Prod.fst <$> extractionSource false terms numerator
          (fun value => -(value.2.1.2 - value.2.2.2) / (value.2.1.1 - value.2.2.1)) (view answer.1, answer.2.2)) =
      (simulateQ privateListOracle (WeightedReduction.badProgram terms g X pk scalar adversary)).run' [] := by
  have run := WeightedAGM.listRun terms (fun masks : F × F => masks.1 • X + masks.2 • g)
    (fun masks => scalar • (masks.1 • X + masks.2 • g)) adversary pk
  rw [← same, simulateQ_map, StateT.run_map, Functor.map_map] at run
  have joined := congrArg
    (fun computation : ProbComp ((Output F M × Transcript K M G) × List (K × (F × F))) =>
      computation >>= fun answer => Prod.fst <$>
        (simulateQ privateListOracle (WeightedAGM.Extract.badFinish terms answer.1.1 answer.1.2)).run answer.2) run
  rw [WeightedCallerHandler.original_run, bind_map_left]
  change _ = Prod.fst <$> (simulateQ privateListOracle (WeightedReduction.badProgram terms g X pk scalar adversary)).run []
  rw [WeightedAGM.Extract.badProgram_finish, simulateQ_bind, StateT.run_bind, map_bind]
  simpa only [WeightedAGM.observe, bind_map_left, bad_extraction_original, output,
    Function.comp_apply, Bool.false_eq_true, ite_false, ite_true] using joined
end Signatures.Runtime.CaliperBackend.WeightedCallerProgram
