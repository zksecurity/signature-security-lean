import Signatures.Runtime.Caliper.BLSFullCorrectness
import Signatures.Runtime.Caliper.BLSCallerExtractionSource
import Signatures.Runtime.Caliper.BLSExtractorSource
import Signatures.Runtime.LazyAGMExtractionQueries

/-! The stored configuration is constant throughout the source query service.
The concrete extractors' erased scalars are the original lazy BLS finish programs,
using the very same private cache left by the caller. -/
namespace Signatures.Runtime.CaliperBackend.BLSCallerHandler
open OracleComp OracleSpec
variable {C G Y : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]

theorem original_run (respond : Bool → val.Value base × C → G) (configuration : C)
    (program : OracleComp (Model.LazyAGM.advSpec (key.Value base) (key.Value base) G) Y)
    (stored : LazyAGM.State (key.Value base) (val.Value base) G) :
    (simulateQ (original respond) program).run (configuration, stored) =
      (fun answer => (answer.1, configuration, answer.2)) <$>
        (simulateQ (LazyAGM.listOracle (fun sample => respond false (sample, configuration))
          (fun sample => respond true (sample, configuration))) program).run stored := by
  induction program using OracleComp.inductionOn generalizing stored with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind q next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [original, StateT.run, bind_map_left, map_bind]
    apply bind_congr
    rintro ⟨answer, nextStore⟩
    exact ih answer nextStore
end Signatures.Runtime.CaliperBackend.BLSCallerHandler

namespace Signatures.Runtime.CaliperBackend.BLSFull
open Caliper BoundedSource OracleComp OracleSpec
variable {M F G : Type} [Field F] [SampleableType F] [DecidableEq M]

noncomputable def goodOriginalExtract (value : (M × (F × (List F × List F))) × (List (M × F) × Model.LazyAGM.Transcript M M G)) : ProbComp F :=
  Prod.fst <$> (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F))
    (LazyAGM.goodFinish ⟨value.1.1, value.1.2.1, value.1.2.2.1, value.1.2.2.2⟩ (LazyAGM.chronological value.2.2))).run value.2.1
noncomputable def badOriginalExtract (value : (M × (F × (List F × List F))) × (List (M × (F × F)) × Model.LazyAGM.Transcript M M G)) : ProbComp F :=
  Prod.fst <$> (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × F))
    (LazyAGM.badFinish ⟨value.1.1, value.1.2.1, value.1.2.2.1, value.1.2.2.2⟩ (LazyAGM.chronological value.2.2))).run value.2.1

variable {w : Nat} {G K A : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [Field (val.Value base)] [SampleableType (val.Value base)]
    [SMul (val.Value base) G] [Add G] [SMul (val.Value base) K]
    (layout : Layouts w (key.Value base) (val.Value base) G K A) (routines : Routines layout)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (drawSource : ProbComp layout.scheme.cache.value.Value)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include drawLaw in
theorem good_extract_original (value : (BLSExtractorFrame.input layout.tokens.good).Value)
    (ready : BLSExtractorFrame.ready layout.tokens.good value) :
    (fun answer => answer.val.1) <$> goodExtract layout routines P comparison correct drawSource value = goodOriginalExtract value.val := by
  have equality := BLSExtractor.good_original layout.tokens routines.zeroValid P comparison correct routines.scalarMul routines.scalarAdd routines.scalarSub routines.scalarDiv
    routines.mulNames.buffers routines.addNames.buffers routines.subNames.buffers (by have := routines.reserve; omega) routines.divNames.buffers drawSource drawLaw value ready
  exact (PFunctor.FreeM.comp_map Prod.fst Subtype.val _).trans (congrArg (fun computation => Prod.fst <$> computation) equality)
include drawLaw in
theorem bad_extract_original (value : (BLSExtractorFrame.input layout.tokens.bad).Value)
    (ready : BLSExtractorFrame.ready layout.tokens.bad value) :
    (fun answer => answer.val.1) <$> badExtract layout routines P comparison correct drawSource value = badOriginalExtract value.val := by
  have equality := BLSExtractor.bad_original layout.tokens routines.zeroValid P comparison correct routines.scalarMul routines.scalarAdd routines.scalarSub routines.scalarNeg routines.scalarDiv
    routines.mulNames.buffers routines.addNames.buffers routines.subNames.buffers (by have := routines.reserve; omega) routines.negNames.buffers routines.divNames.buffers drawSource drawLaw value
    (BLSExtractorFrame.signatureReady_of_ready layout.tokens.bad value ready)
  exact (PFunctor.FreeM.comp_map Prod.fst Subtype.val _).trans (congrArg (fun computation => Prod.fst <$> computation) equality)
end Signatures.Runtime.CaliperBackend.BLSFull
