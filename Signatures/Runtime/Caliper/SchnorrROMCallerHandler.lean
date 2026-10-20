import Signatures.Runtime.Caliper.SchnorrROMCallerPacketBounds

/-! The ROM service in the caller's independent request/reply interface. Both
packet conversions execute Caliper copies, including the complete private state.
Admission is a proved capacity invariant, not a premise about a finished program. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.CallerHandler
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec CallerPackets
variable {w : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (ops : Handler.Operations config)

def code : Interactive.Code w :=
  .seq (.compute (prepare config).code) (.seq (Handler.code config ops) (.compute (finish config).code))

def fallback (value : Packet config) : Reply config :=
  match value.1 with
  | .inl (.inl range) => .inl (.inl ⟨(range.val, 0), ⟨range.property, Nat.two_pow_pos w⟩, Nat.zero_le _⟩)
  | .inl (.inr _) => .inl (.inr ⟨0, trivial⟩)
  | .inr _ => .inr ⟨(value.2.val.1.1.1, 0), value.2.property.1.1.1, trivial⟩

/-- Total extension outside the admitted domain; refinement only uses ready inputs. -/
def source (value : Packet config) : ProbComp (Reply config × config.handler.store.Value) :=
  if valid : ready config value then
    finished config <$> Handler.source config ops (serviceRequest config value valid)
  else pure (fallback config value, value.2)

theorem refines : Interactive.RefinesOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (input config) (output config) (source config ops) (code config ops) := by
  have prepared := (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit
    (prepareService config)).on (fun _ => True)
  have service := Handler.refines config ops
  have converted := (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit
    (finish config)).on (fun _ => True)
  have combined := prepared.seq (service.seq converted (fun _ _ _ _ => trivial)) (by
    intro value _ answer reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst answer
    exact service_ready config value.val value.property)
  intro tape value valid before holds
  have checked := combined tape ⟨value, valid⟩ trivial before holds
  simpa only [source, dite_eq_left valid, pure_bind, bind_pure_comp, code, prepareService,
    Realizer.viewInput, Realizer.viewOutput] using checked

variable (budget : Handler.Budget config ops)
def timeBudget := Handler.timeBudget config ops budget + 154 * width config + 12
def codeBudget := Handler.codeBudget config ops budget + 1020 * width config + 584

theorem time_bound : Interactive.TimeBoundOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (input config) (code config ops) (timeBudget config ops budget) := by
  have prepared := (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit
    (prepareService config)).on (fun _ => True)
  have preparedTime := (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
    (prepareService config) (64 * width config + 6) (fun value => prepare_time config value.val)).on (fun _ => True)
  have serviceTime := Handler.time_bound config ops budget
  have convertedTime := (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
    (finish config) (90 * width config + 6) (finish_time config)).on (fun _ => True)
  have suffix := Interactive.TimeBoundOn.seq (Handler.refines config ops) serviceTime convertedTime
    (fun _ _ _ _ => trivial)
  have combined := (Interactive.TimeBoundOn.seq prepared preparedTime suffix (by
    intro value _ answer reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst answer
    exact service_ready config value.val value.property)).mono
      (larger := timeBudget config ops budget) (by unfold timeBudget; omega)
  intro tape value valid before holds finished reached
  exact combined tape ⟨value, valid⟩ trivial before holds finished reached

theorem code_bound : ((code config ops).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    codeBudget config ops budget := by
  have prepared := prepare_words config
  have converted := finish_words config
  have service := Handler.code_bound config ops budget
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names : WordIO.NamesAccounted ((code config ops).lower (Fresh.port config.handler.sampler.tape))
    (Handler.nameBudget config ops) :=
  ((WordIO.NamesAccounted.compute (prepare_names config)).mono (by unfold Handler.nameBudget; omega)).seq
    ((Handler.names config ops).seq
      ((WordIO.NamesAccounted.compute (finish_names config)).mono (by unfold Handler.nameBudget; omega)))

theorem buffers : ((code config ops).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ max 12 (ops.slots + 3) := by
  have prepared := prepare_buffers config
  have converted := finish_buffers config
  have service := Handler.buffers config ops
  change max (prepare config).code.memBound
    (max ((Handler.code config ops).lower (Fresh.port config.handler.sampler.tape)).memBound
      (finish config).code.memBound) ≤ _
  exact max_le (by omega) (max_le service (by omega))

theorem descriptionFits : ((code config ops).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  .seq config.sampler.wordFits (.compute (prepare config).description_fits)
    (.seq config.sampler.wordFits (Handler.descriptionFits config ops) (.compute (finish config).description_fits))

end Signatures.Runtime.CaliperBackend.SchnorrROM.CallerHandler
