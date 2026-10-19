import Signatures.Runtime.Caliper.BLSFullSource

/-! The original lazy BLS reductions, with the caller's bounded output erased to
the source algebraic-output structure. The shared private cache is passed to the
original finish program without resampling. -/
namespace Signatures.Runtime.CaliperBackend.BLSFull
open Caliper BoundedSource OracleComp OracleSpec
variable {F M G K Y : Type}

def output (value : M × (F × (List F × List F))) : Model.LazyAGM.Output F M :=
  ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩

variable {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [Field (val.Value base)] [SampleableType (val.Value base)]
    [AddCommGroup G] [Module (val.Value base) G]
    (view : Y → key.Value base × (val.Value base × (List (val.Value base) × List (val.Value base))))
    (program : OracleComp (Model.LazyAGM.advSpec (key.Value base) (key.Value base) G) Y)
    (adversary : Model.LazyAGM.Adversary (val.Value base) (key.Value base) (key.Value base) G K)
    (g X : G) (generator pk : K)
    (same : (fun answer => output (view answer)) <$> program = adversary.main pk)

include same in
theorem good_original_finish :
    ((simulateQ (BLSCallerHandler.original (base := base) (key := key) (val := val)
      (fun signing (sample : val.Value base × (G × G)) => sample.1 • (if signing then sample.2.2 else sample.2.1)))
      program).run ((g, X), [], [], []) >>=
        fun answer => goodOriginalExtract (view answer.1, answer.2.2)) =
      BLS.LazyAGM.Reduction.goodReductionList adversary g X generator pk := by
  have run := LazyAGM.listRun (fun scalar : val.Value base => scalar • g) (fun scalar => scalar • X) adversary pk
  rw [← same, simulateQ_map, StateT.run_map, Functor.map_map] at run
  have joined := congrArg
    (fun computation : ProbComp ((Model.LazyAGM.Output (val.Value base) (key.Value base) ×
        Model.LazyAGM.Transcript (key.Value base) (key.Value base) G) × List (key.Value base × val.Value base)) =>
      computation >>= fun answer => Prod.fst <$>
        (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base))
          (LazyAGM.goodFinish answer.1.1 answer.1.2)).run answer.2) run
  rw [BLSCallerHandler.original_run, bind_map_left]
  change _ = Prod.fst <$>
    (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base))
      (BLS.LazyAGM.Reduction.goodProgram g X pk adversary)).run []
  rw [LazyAGM.goodProgram_finish, simulateQ_bind, StateT.run_bind, map_bind]
  simpa only [LazyAGM.observe, bind_map_left, goodOriginalExtract, output, Function.comp_apply, Bool.false_eq_true, ite_false, ite_true] using joined

include same in
theorem bad_original_finish (scalar : val.Value base) :
    ((simulateQ (BLSCallerHandler.original (base := base) (key := key) (val := .pair val val)
      (fun signing (sample : (val.Value base × val.Value base) × (val.Value base × (G × G))) =>
        if signing then sample.2.1 • (sample.1.1 • sample.2.2.2 + sample.1.2 • sample.2.2.1)
        else sample.1.1 • sample.2.2.2 + sample.1.2 • sample.2.2.1))
      program).run ((scalar, g, X), [], [], []) >>=
        fun answer => badOriginalExtract (view answer.1, answer.2.2)) =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base))
        (BLS.LazyAGM.Reduction.badProgram g X pk scalar adversary)).run' [] := by
  have run := LazyAGM.listRun (fun masks : val.Value base × val.Value base => masks.1 • X + masks.2 • g)
    (fun masks => scalar • (masks.1 • X + masks.2 • g)) adversary pk
  rw [← same, simulateQ_map, StateT.run_map, Functor.map_map] at run
  have joined := congrArg
    (fun computation : ProbComp ((Model.LazyAGM.Output (val.Value base) (key.Value base) ×
        Model.LazyAGM.Transcript (key.Value base) (key.Value base) G) × List (key.Value base × (val.Value base × val.Value base))) =>
      computation >>= fun answer => Prod.fst <$>
        (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base))
          (LazyAGM.badFinish answer.1.1 answer.1.2)).run answer.2) run
  rw [BLSCallerHandler.original_run, bind_map_left]
  change _ = Prod.fst <$>
    (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base))
      (BLS.LazyAGM.Reduction.badProgram g X pk scalar adversary)).run []
  rw [LazyAGM.badProgram_finish, simulateQ_bind, StateT.run_bind, map_bind]
  simpa only [LazyAGM.observe, bind_map_left, badOriginalExtract, output, Function.comp_apply, Bool.false_eq_true, ite_false, ite_true] using joined
end Signatures.Runtime.CaliperBackend.BLSFull
