import Proofs.Runtime.Caliper.CoronTerminalFrame

/-! Terminal execution starting at the caller's actual forgery/store result.
Initial memory includes all challenge points, cache and both logs. Routing
copies only the required fields before running the proved cache/extractor. -/
namespace Signatures.Runtime.CaliperBackend.CoronTerminalRouted
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G : Type}
    [DecidableEq M] [SampleableType F] [SMul F G] [Sub G]
    (layout : CoronService.Layouts w M F G randomBound qS) (default : layout.cache.value.Value)
    (sampler : CoronService.Sampler layout) (arithmetic : CoronTerminal.Arithmetic layout)

def code : Interactive.Code w :=
  .seq (.compute (CoronTerminalFrame.route layout default).code) (CoronTerminal.code layout sampler arithmetic)
def denote (value : (CoronTerminalFrame.input layout default).Value) : ProbComp layout.point.Value :=
  CoronTerminal.denote layout sampler arithmetic (CoronTerminalFrame.prepared layout default value)
theorem refines : Interactive.Refines layout.port .unit (CoronTerminalFrame.input layout default).representation
    layout.point.representation (denote layout default sampler arithmetic) (code layout default sampler arithmetic) := by
  have composed := (Interactive.Refines.compute layout.port .unit (CoronTerminalFrame.route layout default)).seq
    (CoronTerminal.refines layout sampler arithmetic)
  convert composed using 1
  · funext value
    simp only [pure_bind]
    rfl
  · rfl

def timeBudget : Nat := CoronTerminal.timeBudget layout sampler arithmetic + 8 * (CoronTerminal.input layout).representation.encoding.words
def codeBudget : Nat := CoronTerminal.codeBudget layout sampler arithmetic + 26 * (CoronTerminal.input layout).representation.encoding.words + 16
def memoryBudget : Nat := 5 * codeBudget layout sampler arithmetic + 4 * CoronTerminal.nameBudget layout sampler arithmetic + 3 +
  (CoronTerminalFrame.input layout default).representation.encoding.words + timeBudget layout sampler arithmetic

theorem time_bound : Interactive.TimeBound layout.port .unit (CoronTerminalFrame.input layout default).representation
    (code layout default sampler arithmetic) (timeBudget layout sampler arithmetic) := by
  have routed := Interactive.TimeBound.compute (port := layout.port) (cost := .unit) (CoronTerminalFrame.route layout default)
    _ (CoronTerminalFrame.route_time layout default)
  exact (routed.seq (Interactive.Refines.compute layout.port .unit (CoronTerminalFrame.route layout default))
    (CoronTerminal.time_bound layout sampler arithmetic)).mono (by unfold timeBudget; omega)
theorem code_words : ((code layout default sampler arithmetic).lower layout.port).descriptionWords ≤ codeBudget layout sampler arithmetic := by
  have routed := CoronTerminalFrame.route_words layout default
  have terminal := CoronTerminal.code_words layout sampler arithmetic
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega
theorem names : WordIO.NamesAccounted ((code layout default sampler arithmetic).lower layout.port)
    (CoronTerminal.nameBudget layout sampler arithmetic) :=
  (WordIO.NamesAccounted.compute (CoronTerminalFrame.route_names layout default _)).seq (CoronTerminal.names layout sampler arithmetic)
theorem descriptionFits : ((code layout default sampler arithmetic).lower layout.port).DescriptionFits :=
  .seq layout.cache.wordFits (.compute (CoronTerminalFrame.route layout default).description_fits)
    (CoronTerminal.descriptionFits layout sampler arithmetic)

theorem source_eq (value : (CoronTerminalFrame.input layout default).Value) :
    Subtype.val <$> denote layout default sampler arithmetic value =
      (fun result => value.val.1.val.2 - result.1.1 • value.val.2.val.1.2.1) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × Fin (qS.val + 1)))
          (.inr value.val.1.val.1)).run value.val.2.val.2.1 :=
  CoronTerminal.source_eq layout sampler arithmetic (CoronTerminalFrame.prepared layout default value)

theorem within : Interactive.Within layout.port (CoronTerminalFrame.input layout default) layout.point
    (codeBudget layout sampler arithmetic) (memoryBudget layout default sampler arithmetic) (timeBudget layout sampler arithmetic)
    (fun value => (fun result => value.val.1.val.2 - result.1.1 • value.val.2.val.1.2.1) <$>
      ((BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × Fin (qS.val + 1)))
        (.inr value.val.1.val.1)).run value.val.2.val.2.1) :=
  (Interactive.within_of_refines_accounted (refines layout default sampler arithmetic) (time_bound layout default sampler arithmetic)
    (code_words layout default sampler arithmetic) (names layout default sampler arithmetic) (descriptionFits layout default sampler arithmetic)).congr
      (source_eq layout default sampler arithmetic)

end Signatures.Runtime.CaliperBackend.CoronTerminalRouted
