import Proofs.Runtime.Caliper.SchnorrROMNonzeroSigningHandlerRoute
import Proofs.Runtime.Caliper.SchnorrROMNonzeroSigningUnits

/-! The executed nonzero signing branch on the full signing frame
`config.handler.input → config.handler.output`.

The two field draws `c, z` are the full-field signer's replayed pair
(`Signing.Handler.retained`), and the nonce `a` is a third replayed draw through
the private service with the nonzero caller. All three are uniform requests
replayed on the shared raw tape, exactly as `liftRandom` queries are replayed by
the list backend. The deterministic suffix is `NonzeroSigning.implementation`.
Every frame permutation and retained copy is executed code. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.NonzeroSigning
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

/-- The replayed nonzero-scalar caller of the enumerated sampler. -/
def nonzeroCaller [Zero F] (positive : 0 < config.sampler.bound) : PrivateSampler.Caller config.handler.sampler :=
  PrivateSampler.Enumerated.Nonzero.caller config.sampler positive

/-- Signing readiness: one managed insertion slot (from the input layout) and
three reserved tape slots for the three replayed draws. -/
def ready (value : config.handler.input.Value) : Prop :=
  PrivateHandler.Reserved config.handler.sampler.tape 3 (Signing.Handler.tapes config.handler value)

section Code
variable [Zero F] [SMul F G] [Sub G] [Add F] [DecidableEq M] [DecidableEq G]
    (ops : Handler.Operations config) (arith : Arithmetic config) (positive : 0 < config.sampler.bound)

theorem coreNameFits : (implementation config ops arith).program.savedBuffer < 2 ^ w := by
  have := buffers config ops arith
  have := slots_reserve config ops arith
  have := config.sampler.wordFits
  unfold Realizer.savedBuffer
  omega

/-- The core with the LIVE table and the tapes retained by executed copying. -/
def retainedCore := (implementation config ops arith).program.retain (by decide) config.handler.saved.representation
  config.sampler.wordFits (coreNameFits config ops arith) (work config).fits config.handler.finished.fits

def result (value : (Reply.scalarOutput config.handler.sampler.tape).Value ×
    (config.handler.core.arithmetic.scalars.Value × config.handler.context.Value)) : config.handler.output.Value :=
  Signing.Handler.finishValue config.handler
    (⟨NonzeroSigning.value (workValue config value).1.val,
      (implementation config ops arith).preserves (workValue config value).1.val (workValue config value).1.property⟩,
     (workValue config value).2)

/-- Route the third draw into the core frame, run the retained core and view the
result as the handler output. -/
def finish : Realizer .unit (drawn config) config.handler.output.representation (result config ops arith) :=
  ((workRoute config).then (retainedCore config ops arith)).viewOutput config.handler.output.representation
    (result config ops arith) (fun _ => Signing.Handler.finish_bytes config.handler _)

/-- The retained third (nonzero) draw. -/
def retainedNonzero := Interactive.retain
  (PrivateSampler.Service.code config.handler.sampler (nonzeroCaller config positive) trivial 1)
  (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape)
    (PrivateSampler.Service.code config.handler.sampler (nonzeroCaller config positive) trivial 1))
  (Read.tapes config.handler.sampler.tape).representation.encoding.words
  (Reply.scalarOutput config.handler.sampler.tape).representation.encoding.words
  (pairCtx config).encoding.words

/-- The executed nonzero signing branch. -/
def code : Interactive.Code w :=
  .seq (.compute (Signing.Handler.prepare config.handler).code)
    (.seq (Signing.Handler.retained config.handler trivial (PrivateSampler.Enumerated.caller config.sampler) 1)
      (.seq (.compute (midRoute config).code)
        (.seq (retainedNonzero config positive) (.compute (finish config ops arith).code))))

/-- The source program of the executed branch: the replayed pair, the replayed
nonzero draw, then the deterministic suffix. -/
def source (value : config.handler.input.Value) : ProbComp config.handler.output.Value := do
  let sampled ← PrivateSampler.Pair.source config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler) trivial 1
    (Signing.Handler.tapes config.handler value)
  let moved := midValue config (sampled, Signing.Handler.context config.handler value)
  let nonce ← PrivateSampler.Service.source config.handler.sampler (nonzeroCaller config positive) trivial 1 moved.1
  pure (result config ops arith (nonce, moved.2))

omit [Zero F] [SMul F G] [Sub G] [Add F] [DecidableEq M] [DecidableEq G] in
theorem pair_ready (value : config.handler.input.Value) (valid : ready config value) :
    PrivateSampler.Pair.ready config.handler.sampler 1 (Signing.Handler.tapes config.handler value) := by
  unfold ready PrivateHandler.Reserved at valid
  change (Signing.Handler.tapes config.handler value).val.1.length + (1 + 1) ≤ config.handler.sampler.tape.capacity
  omega

omit [SMul F G] [Sub G] [Add F] [DecidableEq M] [DecidableEq G] in
theorem nonce_ready (value : config.handler.input.Value) (valid : ready config value)
    (sampled : (PrivateSampler.Pair.output config.handler.sampler).Value)
    (reached : sampled ∈ support (PrivateSampler.Pair.source config.handler.sampler
      (PrivateSampler.Enumerated.caller config.sampler) trivial 1 (Signing.Handler.tapes config.handler value))) :
    PrivateSampler.Service.ready config.handler.sampler 1 (midValue config (sampled, Signing.Handler.context config.handler value)).1 :=
  PrivateSampler.Pair.reserved_after config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler) trivial 1 1
    (Signing.Handler.tapes config.handler value) valid sampled reached

theorem refines : Interactive.RefinesOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    config.handler.input.representation config.handler.output.representation
    (source config ops arith positive) (code config ops arith positive) := by
  have nonce := (PrivateSampler.Service.refines config.handler.sampler (nonzeroCaller config positive) trivial 1).retain
    (by decide) (pairCtx config) config.sampler.wordFits (middle config).fits (drawn config).fits
  have finished := nonce.seq
    ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (finish config ops arith)).on (fun _ => True))
    (by intros; trivial)
  have moved := ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (midRoute config)).on
    (fun value => PrivateSampler.Service.ready config.handler.sampler 1 (midValue config value).1)).seq finished (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact valid)
  have pairRefines : Interactive.RefinesOn
      (fun value : PrivateSampler.Store config.handler.sampler × config.handler.context.Value =>
        PrivateHandler.Reserved config.handler.sampler.tape 3 value.1)
      (Fresh.port config.handler.sampler.tape) .unit config.handler.prepared config.handler.sampled
      (fun value => (fun answer => (answer, value.2)) <$> PrivateSampler.Pair.source config.handler.sampler
        (PrivateSampler.Enumerated.caller config.sampler) trivial 1 value.1)
      (Signing.Handler.retained config.handler trivial (PrivateSampler.Enumerated.caller config.sampler) 1) :=
    fun tape value valid before holds =>
      Signing.Handler.retained_refines config.handler trivial (PrivateSampler.Enumerated.caller config.sampler) 1 tape value
        (by unfold PrivateHandler.Reserved at valid
            change value.1.val.1.length + (1 + 1) ≤ config.handler.sampler.tape.capacity
            omega) before holds
  have sampled := pairRefines.seq moved (by
    intro value valid answer reached
    simp only [support_map, Set.mem_image] at reached
    obtain ⟨sampled, supported, rfl⟩ := reached
    exact PrivateSampler.Pair.reserved_after config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler)
      trivial 1 1 value.1 valid sampled supported)
  have combined := ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit
    (Signing.Handler.prepare config.handler)).on (ready config)).seq sampled (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact valid)
  convert combined using 1
  · funext value
    simp only [source, pure_bind, bind_pure_comp, Functor.map_map, bind_map_left]
    rfl
  · rfl

theorem preserves_live (value : config.handler.input.Value) (answer : config.handler.output.Value)
    (reached : answer ∈ support (source config ops arith positive value)) :
    answer.val.2.1.2.2 = value.val.2.1.2.2 := by
  simp only [source, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨sampled, _, nonce, _, rfl⟩ := reached
  rfl

theorem managed_length (value : config.handler.input.Value) (answer : config.handler.output.Value)
    (reached : answer ∈ support (source config ops arith positive value)) :
    answer.val.2.1.2.1.length ≤ value.val.2.1.2.1.length + 1 := by
  simp only [source, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨sampled, _, nonce, _, rfl⟩ := reached
  exact Signing.Cache.length _

/-- Three replayed draws consume at most three reserved tape slots. -/
theorem reserved_after (remaining : Nat) (value : config.handler.input.Value)
    (room : PrivateHandler.Reserved config.handler.sampler.tape (3 + remaining) (Signing.Handler.tapes config.handler value))
    (answer : config.handler.output.Value) (reached : answer ∈ support (source config ops arith positive value)) :
    answer.val.2.2.1.length + remaining ≤ config.handler.sampler.tape.capacity := by
  simp only [source, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨sampled, supported, nonce, nonceSupported, rfl⟩ := reached
  have afterPair := PrivateSampler.Pair.reserved_after config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler)
    trivial 1 (1 + remaining) (Signing.Handler.tapes config.handler value)
    (by unfold PrivateHandler.Reserved at room ⊢; omega) sampled supported
  exact PrivateSampler.Service.reserved_after config.handler.sampler (nonzeroCaller config positive) trivial 1 remaining
    (midValue config (sampled, Signing.Handler.context config.handler value)).1
    afterPair nonce nonceSupported

end Code
end Signatures.Runtime.CaliperBackend.SchnorrROM.NonzeroSigning
