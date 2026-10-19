import Signatures.Runtime.Caliper.CoronTerminalRouted
import Signatures.Runtime.Caliper.SumContextBounds

/-! Executed terminal dispatch for the ordinary co-CDH caller. Distribution
moves union padding across the store by copying. Returns route to extraction;
cutoffs emit a represented fallback without a cache lookup or random draw. -/
namespace Signatures.Runtime.CaliperBackend.CoronCallerFinish
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G P : Type}
    (layout : CoronService.Layouts w M F G randomBound qS) (pending : Representation w P)
    (fits : 1 + max (CoronTerminalFrame.forgery layout).representation.encoding.words pending.encoding.words +
      layout.service.store.representation.encoding.words < 2 ^ w)

abbrev Packet := ((CoronTerminalFrame.forgery layout).Value ⊕ P) × layout.service.store.Value
def input : Representation w (Packet (P := P) layout) :=
  SumContext.input (CoronTerminalFrame.forgery layout).representation pending layout.service.store.representation layout.cache.wordFits fits
def cutoff : Representation w (P × layout.service.store.Value) := pending.prod layout.service.store.representation (by omega)
theorem choiceFits : 1 + max (CoronTerminalFrame.plain layout).encoding.words (cutoff layout pending fits).encoding.words < 2 ^ w := by
  change 1 + max ((CoronTerminalFrame.forgery layout).representation.encoding.words + layout.service.store.representation.encoding.words)
    (pending.encoding.words + layout.service.store.representation.encoding.words) < 2 ^ w
  omega
def distribute := SumContext.distribute (CoronTerminalFrame.forgery layout).representation pending
  layout.service.store.representation layout.cache.wordFits fits

def fallback (point : layout.point.Value) : Realizer .unit (cutoff layout pending fits) layout.point.representation (fun _ => point) :=
  (Implementation.constant (Layout.all (cutoff layout pending fits)) layout.point point layout.cache.wordFits).program.viewInput
    (cutoff layout pending fits) (fun value => ⟨value, trivial⟩) (fun _ => rfl)
theorem fallback_time (point : layout.point.Value) (value) :
    (fallback layout pending fits point).time value ≤ 8 * layout.point.representation.encoding.words :=
  (Implementation.constant_bounded (Layout.all (cutoff layout pending fits)) layout.point point layout.cache.wordFits).time_le ⟨value, trivial⟩
theorem fallback_words (point : layout.point.Value) :
    descriptionWords (fallback layout pending fits point).code ≤ 26 * layout.point.representation.encoding.words + 14 :=
  (Implementation.constant_bounded (Layout.all (cutoff layout pending fits)) layout.point point layout.cache.wordFits).code_le
theorem fallback_names (point : layout.point.Value) (slots : Nat) : NamesAccounted (fallback layout pending fits point).code slots :=
  Implementation.constant_names (Layout.all (cutoff layout pending fits)) layout.point point layout.cache.wordFits slots

variable [DecidableEq M] (default : layout.cache.value.Value)
def ready (value : Packet (P := P) layout) : Prop :=
  Sum.elim (CoronTerminalFrame.ready layout default) (fun _ => True) (SumContext.view value)
instance : DecidablePred (ready (P := P) layout default) := by
  rintro ⟨result | next, saved⟩
  · exact inferInstanceAs (Decidable (CoronTerminalFrame.ready layout default (result, saved)))
  · exact instDecidableTrue
def admitted : Layout w (Packet (P := P) layout) where
  valid := ready layout default
  representation := (input layout pending fits).restrict (ready layout default)

variable [SampleableType F] [SMul F G] [Sub G]
    (sampler : CoronService.Sampler layout) (arithmetic : CoronTerminal.Arithmetic layout) (point : layout.point.Value)

/-- A total source extension; unready returns have no execution claim. -/
def returned (value : CoronTerminalFrame.Packet layout) : ProbComp layout.point.Value :=
  if valid : CoronTerminalFrame.ready layout default value then
    CoronTerminalRouted.denote layout default sampler arithmetic ⟨value, valid⟩
  else pure point
def denote (value : Packet (P := P) layout) : ProbComp layout.point.Value :=
  Sum.elim (returned layout default sampler arithmetic point) (fun _ => pure point) (SumContext.view value)
def code : Interactive.Code w :=
  .seq (.compute (distribute layout pending fits).code)
    (Interactive.dispatch (CoronTerminalRouted.code layout default sampler arithmetic) (.compute (fallback layout pending fits point).code)
      (CoronTerminalFrame.plain layout).encoding.words (cutoff layout pending fits).encoding.words)

theorem returned_refines : Interactive.RefinesOn (CoronTerminalFrame.ready layout default) layout.port .unit
    (CoronTerminalFrame.plain layout) layout.point.representation (returned layout default sampler arithmetic point)
    (CoronTerminalRouted.code layout default sampler arithmetic) := by
  intro tape value valid before holds
  simpa only [returned, dite_eq_left valid] using
    CoronTerminalRouted.refines layout default sampler arithmetic tape ⟨value, valid⟩ before holds

omit [SampleableType F] [SMul F G] [Sub G] in
theorem distributed_ready (value : Packet (P := P) layout) (valid : ready layout default value)
    (answer) (reached : answer ∈ support (pure (SumContext.view value) : ProbComp _)) :
    Sum.elim (CoronTerminalFrame.ready layout default) (fun _ => True) answer := by
  simp only [support_pure, Set.mem_singleton_iff] at reached
  subst answer
  exact valid

theorem refines : Interactive.RefinesOn (ready layout default) layout.port .unit (input layout pending fits) layout.point.representation
    (denote layout default sampler arithmetic point) (code layout pending fits default sampler arithmetic point) := by
  have branches := Interactive.RefinesOn.dispatch (CoronTerminalFrame.plain layout) (cutoff layout pending fits) layout.point.representation
    (returned_refines layout default sampler arithmetic point)
    ((Interactive.Refines.compute layout.port .unit (fallback layout pending fits point)).on (fun _ => True))
    (width_pos layout.cache.wordFits) (choiceFits layout pending fits)
  have composed := ((Interactive.Refines.compute layout.port .unit (distribute layout pending fits)).on (ready layout default)).seq
    branches (distributed_ready layout default)
  convert composed using 1
  · rfl
  · funext value
    simp only [pure_bind]
    rfl
  · rfl

omit [SampleableType F] [SMul F G] [Sub G] in
theorem ready_of_postcondition {fuel : Nat} {before after : layout.service.store.Value}
    (post : BLSCaller.Postcondition layout.service fuel before after)
    (room : before.val.2.1.length + fuel + 1 ≤ layout.service.cache.capacityPred + 1)
    (result : (CoronTerminalFrame.forgery layout).Value ⊕ P) : ready layout default (result, after) := by
  cases result with
  | inl result => exact CoronTerminalFrame.ready_of_postcondition layout default post room result
  | inr _ => trivial

end Signatures.Runtime.CaliperBackend.CoronCallerFinish
