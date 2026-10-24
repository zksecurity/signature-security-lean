import Proofs.Runtime.Caliper.CoronCallerFinish

/-! Complete termination overhead, including relocation of union padding,
both stored branches, the discarded store, and every intermediate allocation.
Only the selected branch contributes execution time. -/
namespace Signatures.Runtime.CaliperBackend.CoronCallerFinish
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G P : Type}
    (layout : CoronService.Layouts w M F G randomBound qS) (pending : Representation w P)
    (fits : 1 + max (CoronTerminalFrame.forgery layout).representation.encoding.words pending.encoding.words +
      layout.service.store.representation.encoding.words < 2 ^ w)

theorem frame_sizes :
    (CoronTerminalFrame.plain layout).encoding.words ≤ (input layout pending fits).encoding.words ∧
    (cutoff layout pending fits).encoding.words ≤ (input layout pending fits).encoding.words := by
  change _ + _ ≤ 1 + max _ _ + _ ∧ _ + _ ≤ 1 + max _ _ + _
  omega
theorem distribute_time (value) : (distribute layout pending fits).time value ≤
    24 * (input layout pending fits).encoding.words + 2 :=
  SumContext.time _ _ _ _ _ value
theorem distribute_words : descriptionWords (distribute layout pending fits).code ≤
    156 * (input layout pending fits).encoding.words + 95 := SumContext.words _ _ _ _ _
theorem distribute_names : NamesAccounted (distribute layout pending fits).code 3 :=
  SumContext.names _ _ _ _ _

variable [DecidableEq M] [SampleableType F] [SMul F G] [Sub G]
    (default : layout.cache.value.Value) (sampler : CoronService.Sampler layout)
    (arithmetic : CoronTerminal.Arithmetic layout) (point : layout.point.Value)

def timeBudget : Nat := CoronTerminalRouted.timeBudget layout sampler arithmetic +
  8 * layout.point.representation.encoding.words + 32 * (input layout pending fits).encoding.words + 4
def codeBudget : Nat := CoronTerminalRouted.codeBudget layout sampler arithmetic +
  26 * layout.point.representation.encoding.words + 208 * (input layout pending fits).encoding.words + 152
def memoryBudget : Nat := 5 * codeBudget layout pending fits sampler arithmetic +
  4 * CoronTerminal.nameBudget layout sampler arithmetic + 3 + (input layout pending fits).encoding.words +
    timeBudget layout pending fits sampler arithmetic

theorem time_bound : Interactive.TimeBoundOn (ready layout default) layout.port .unit (input layout pending fits)
    (code layout pending fits default sampler arithmetic point) (timeBudget layout pending fits sampler arithmetic) := by
  have returnedBound : Interactive.TimeBoundOn (CoronTerminalFrame.ready layout default) layout.port .unit
      (CoronTerminalFrame.plain layout) (CoronTerminalRouted.code layout default sampler arithmetic)
      (CoronTerminalRouted.timeBudget layout sampler arithmetic) :=
    fun tape value valid before holds =>
      CoronTerminalRouted.time_bound layout default sampler arithmetic tape ⟨value, valid⟩ before holds
  have branches := Interactive.TimeBoundOn.dispatch (CoronTerminalFrame.plain layout) (cutoff layout pending fits)
    returnedBound ((Interactive.TimeBound.compute (port := layout.port) (cost := .unit)
      (fallback layout pending fits point) _ (fallback_time layout pending fits point)).on (fun _ => True))
    (width_pos layout.cache.wordFits) (choiceFits layout pending fits)
  have composed := Interactive.TimeBoundOn.seq
    ((Interactive.Refines.compute layout.port .unit (distribute layout pending fits)).on (ready layout default))
    ((Interactive.TimeBound.compute (port := layout.port) (cost := .unit) (distribute layout pending fits)
      _ (distribute_time layout pending fits)).on (ready layout default)) branches (distributed_ready layout default)
  apply composed.mono
  rw [Interactive.dispatchTime_unit]
  have := frame_sizes layout pending fits
  unfold timeBudget
  omega

theorem code_words : ((code layout pending fits default sampler arithmetic point).lower layout.port).descriptionWords ≤
    codeBudget layout pending fits sampler arithmetic := by
  have relocated := distribute_words layout pending fits
  have success := CoronTerminalRouted.code_words layout default sampler arithmetic
  have stopped := fallback_words layout pending fits point
  have := frame_sizes layout pending fits
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute,
    Interactive.dispatch_descriptionWords]
  unfold codeBudget
  omega

theorem names : WordIO.NamesAccounted ((code layout pending fits default sampler arithmetic point).lower layout.port)
    (CoronTerminal.nameBudget layout sampler arithmetic) := by
  have relocated := (distribute_names layout pending fits).mono (b := CoronTerminal.nameBudget layout sampler arithmetic)
    (by unfold CoronTerminal.nameBudget; omega)
  exact (WordIO.NamesAccounted.compute relocated).seq (Interactive.dispatch_names layout.port
    (left := CoronTerminalRouted.code layout default sampler arithmetic)
    (right := .compute (fallback layout pending fits point).code)
    (CoronTerminalRouted.names layout default sampler arithmetic)
    (.compute (fallback_names layout pending fits point _)) _ _)

theorem descriptionFits : ((code layout pending fits default sampler arithmetic point).lower layout.port).DescriptionFits :=
  .seq layout.cache.wordFits (.compute (distribute layout pending fits).description_fits)
    (Interactive.dispatch_descriptionFits layout.port _ _ _ _ layout.cache.wordFits
      (CoronTerminalRouted.descriptionFits layout default sampler arithmetic)
      (.compute (fallback layout pending fits point).description_fits)
      (CoronTerminalFrame.plain layout).fits (cutoff layout pending fits).fits)

theorem within : Interactive.Within layout.port (admitted layout pending fits default) layout.point
    (codeBudget layout pending fits sampler arithmetic) (memoryBudget layout pending fits sampler arithmetic)
    (timeBudget layout pending fits sampler arithmetic)
    (fun value => Subtype.val <$> denote layout default sampler arithmetic point value.val) :=
  Interactive.within_of_refines_accounted (refines layout pending fits default sampler arithmetic point).restrict
    (time_bound layout pending fits default sampler arithmetic point).restrict
    (code_words layout pending fits default sampler arithmetic point) (names layout pending fits default sampler arithmetic point)
    (descriptionFits layout pending fits default sampler arithmetic point)

theorem source_return (value : CoronTerminalFrame.Packet layout) (valid : CoronTerminalFrame.ready layout default value) :
    Subtype.val <$> denote (P := P) layout default sampler arithmetic point (.inl value.1, value.2) =
      (fun result => value.1.val.2 - result.1.1 • value.2.val.1.2.1) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × Fin (qS.val + 1)))
          (.inr value.1.val.1)).run value.2.val.2.1 := by
  change Subtype.val <$> returned layout default sampler arithmetic point value = _
  rw [returned, dite_eq_left valid]
  exact CoronTerminalRouted.source_eq layout default sampler arithmetic ⟨value, valid⟩

theorem source_cutoff (next : P) (saved : layout.service.store.Value) :
    Subtype.val <$> denote layout default sampler arithmetic point (.inr next, saved) = pure point.val := by
  change Subtype.val <$> (pure point : ProbComp _) = _
  rw [map_pure]

end Signatures.Runtime.CaliperBackend.CoronCallerFinish
