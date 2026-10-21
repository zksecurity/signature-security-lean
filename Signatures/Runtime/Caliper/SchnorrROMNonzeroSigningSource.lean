import Signatures.Runtime.Caliper.SchnorrROMNonzeroSigningHandler
import Signatures.Runtime.Caliper.SchnorrROMEnumeratedSigning
import Signatures.Runtime.SchnorrNonzeroListPass

/-! Exact correspondence of the executed nonzero signing branch with the
nonzero list backend `Schnorr.NonzeroListROM.handler (.inr msg)`, interpreted on
the shared replay tape.

The list backend lifts the three uniform draws of `NonzeroNonce.simTranscript`
with `liftRandom`; the shared-tape interpreter replays each of them on the raw
tape. The executed branch performs the same three replayed draws (two through
the enumerated field caller, one through the nonzero caller), so the equality is
exact query-tree equality for every ready input. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.NonzeroSigning
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec

/-! ### Replay of a lifted uniform program -/

section Replay
variable {F A : Type} [Field F] [SampleableType F]

/-- Replaying a lifted uniform program on the shared tape is the private
replay oracle on that program. -/
theorem tapeRun_liftRandom (main : ProbComp A) (tape : Schnorr.ListROM.Shared.Tape F) :
    Schnorr.ListROM.Shared.tapeRun (Schnorr.liftRandom main) tape =
      (fun result => (result.1, result.2.saved, result.2.remaining)) <$>
        (simulateQ Schnorr.RawTape.Private.oracle main).run ⟨tape.1, tape.2⟩ := by
  rw [Schnorr.RawTape.Private.simulate_source _root_.Schnorr.LazyROM.sample (fun _ => rfl)]
  rfl

omit [Field F] [SampleableType F] in
theorem liftRandom_bind {B : Type} (main : ProbComp A) (next : A → ProbComp B) :
    Schnorr.liftRandom (F := F) (main >>= next) = Schnorr.liftRandom main >>= fun a => Schnorr.liftRandom (next a) := by
  unfold Schnorr.liftRandom
  rw [simulateQ_bind]

omit [Field F] [SampleableType F] in
theorem liftRandom_pure (a : A) : Schnorr.liftRandom (F := F) (pure a : ProbComp A) = pure a := by
  unfold Schnorr.liftRandom
  rw [simulateQ_pure]

end Replay

section Draws
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G) [Field F]

/-- The replayed nonzero draw is the lifted canonical draw of `Fˣ`, replayed on
the shared tape. -/
theorem nonce_source (saved : PrivateSampler.Store config.handler.sampler)
    (valid : PrivateSampler.Service.ready config.handler.sampler 1 saved) :
    let := PrivateSampler.Enumerated.sampleable config.sampler
    let := PrivateSampler.Enumerated.Nonzero.unitsSampleable config.sampler
    Subtype.val <$> PrivateSampler.Service.source config.handler.sampler
        (nonzeroCaller config (PrivateSampler.Enumerated.Nonzero.bound_pos config.sampler)) trivial 1 saved =
      Schnorr.ListROM.Shared.tapeRun (Schnorr.liftRandom ((fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ : ProbComp Fˣ))) saved.val := by
  intro _ _
  rw [PrivateSampler.Service.source_original config.handler.sampler
    (nonzeroCaller config (PrivateSampler.Enumerated.Nonzero.bound_pos config.sampler)) trivial 1
    (PrivateSampler.Enumerated.Nonzero.terminates config.sampler (PrivateSampler.Enumerated.Nonzero.bound_pos config.sampler))
    saved valid, tapeRun_liftRandom]
  have same := congrArg (fun main : ProbComp F =>
    (simulateQ Schnorr.RawTape.Private.oracle main).run (PrivateHandler.stored config.handler.sampler.tape saved))
    (PrivateSampler.Enumerated.Nonzero.samples config.sampler (PrivateSampler.Service.unit config.handler.sampler))
  simp only [simulateQ_map, StateT.run_map] at same
  have mapped := congrArg (Functor.map (fun result : F × Schnorr.RawTape.State F =>
    (result.1, result.2.saved, result.2.remaining))) same
  simp only [Functor.map_map, simulateQ_map, StateT.run_map] at mapped ⊢
  exact mapped

/-- The replayed field pair is two lifted canonical field draws, replayed in
order on the shared tape. -/
theorem pair_source (saved : PrivateSampler.Store config.handler.sampler)
    (valid : PrivateSampler.Pair.ready config.handler.sampler 1 saved) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    Subtype.val <$> PrivateSampler.Pair.source config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler)
        trivial 1 saved = (do
      let first ← Schnorr.ListROM.Shared.tapeRun (Schnorr.liftRandom ($ᵗ F : ProbComp F)) saved.val
      (fun second => (first.1, second)) <$>
        Schnorr.ListROM.Shared.tapeRun (Schnorr.liftRandom ($ᵗ F : ProbComp F)) first.2) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  exact PrivateSampler.Pair.scalar_source config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler) trivial 1
    (PrivateSampler.Enumerated.terminates config.sampler)
    (PrivateSampler.Enumerated.samples config.sampler (PrivateSampler.Service.unit config.handler.sampler)) saved valid

end Draws

/-! ### The deterministic part of nonzero signing -/

section Deterministic
variable {M F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] [DecidableEq M]

/-- The signature and programmed managed table for draws `c, z, a`. -/
def rawSign (g pk : G) (msg : M) (managed : Signing.Table M F G) (c z a : F) : (G × F) × Signing.Table M F G :=
  let commitment := z • g - c • pk
  let transcript : G × F × F := if commitment = 0 then (a • g, c, z + a) else (commitment, c, z)
  ((transcript.1, transcript.2.2), CacheProgramming.value (msg, transcript.1) transcript.2.1 managed)

theorem update_value (key : M × G) (challenge : F) (managed : Signing.Table M F G) :
    Signing.Cache.update (key, challenge, managed, ()) = CacheProgramming.value key challenge managed := by
  rw [Signing.Cache.update_original (G₂ := G) (K := M)]
  exact Schnorr.ListROM.NativeCache.programming_value (G₂ := G) (K := M) PrimitiveCosts.unit key challenge managed

/-- The executed suffix computes `rawSign`, with the configuration retained. -/
theorem value_eq (a c z : F) (g pk : G) (msg : M) (managed : Signing.Table M F G) :
    value (a, (c, z), g, pk, msg, managed) =
      ((rawSign g pk msg managed c z a).1, (g, pk), (rawSign g pk msg managed c z a).2) := by
  by_cases zero : z • g - c • pk = 0 <;>
    simp only [value, Signing.Cache.value, assemble, repaired, commitValue, zeroTest, Signing.Arithmetic.commitment,
      rawSign, sub_self, zero, decide_true, decide_false, update_value,
      Bool.false_eq_true, ↓reduceIte]

variable [SampleableType F] [SampleableType Fˣ]

omit [DecidableEq F] in
theorem source_eq (g pk : G) (msg : M) (managed : Signing.Table M F G) :
    Schnorr.NonzeroSigning.source g pk msg managed = (do
      let c ← ($ᵗ F : ProbComp F)
      let z ← ($ᵗ F : ProbComp F)
      let a ← (fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ : ProbComp Fˣ)
      pure (rawSign g pk msg managed c z a)) := by
  simp only [Schnorr.NonzeroSigning.source, _root_.Schnorr.NonzeroNonce.simTranscript, bind_assoc, bind_map_left]
  congr 1
  funext c
  congr 1
  funext z
  congr 1
  funext a
  by_cases zero : z • g - c • pk = 0 <;> simp only [zero, ↓reduceIte, pure_bind, rawSign]

end Deterministic

/-! ### Source correspondence -/

section Main
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)
    [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] [DecidableEq M]
    (ops : Handler.Operations config) (arith : Arithmetic config)

/-- **Source correspondence.** For every ready signing frame, the executed
nonzero signing branch has exactly the nonzero list backend's signing oracle,
interpreted on the shared replay tape, as its source program. -/
theorem source_original (input : config.handler.input.Value) (valid : ready config input) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    letI := PrivateSampler.Enumerated.Nonzero.unitsSampleable config.sampler
    Subtype.val <$> source config ops arith (PrivateSampler.Enumerated.Nonzero.bound_pos config.sampler) input =
      (Schnorr.ListROM.Shared.interpret
        (Schnorr.NonzeroListROM.handler (G₂ := G) (K := M) (.inr input.val.1))).run input.val.2 := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  let := PrivateSampler.Enumerated.Nonzero.unitsSampleable config.sampler
  have rhs : (Schnorr.ListROM.Shared.interpret
      (Schnorr.NonzeroListROM.handler (G₂ := G) (K := M) (.inr input.val.1))).run input.val.2 = (do
        let first ← Schnorr.ListROM.Shared.tapeRun (Schnorr.liftRandom ($ᵗ F : ProbComp F)) input.val.2.2
        let second ← Schnorr.ListROM.Shared.tapeRun (Schnorr.liftRandom ($ᵗ F : ProbComp F)) first.2
        let third ← Schnorr.ListROM.Shared.tapeRun
          (Schnorr.liftRandom ((fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ : ProbComp Fˣ))) second.2
        let signed := rawSign input.val.2.1.1.1 input.val.2.1.1.2 input.val.1 input.val.2.1.2.1 first.1 second.1 third.1
        pure (signed.1, (input.val.2.1.1, signed.2, input.val.2.1.2.2), third.2)) := by
    change (fun p => (p.1.1, p.1.2, p.2)) <$> Schnorr.ListROM.Shared.tapeRun
      ((fun p => (p.1, (input.val.2.1.1, p.2, input.val.2.1.2.2))) <$>
        Schnorr.liftRandom (Schnorr.NonzeroSigning.source input.val.2.1.1.1 input.val.2.1.1.2 input.val.1
          input.val.2.1.2.1)) input.val.2.2 = _
    simp only [source_eq, liftRandom_bind, liftRandom_pure, Schnorr.ListROM.Shared.tapeRun_bind,
      Schnorr.ListROM.Shared.tapeRun_pure, map_bind, map_pure]
  rw [rhs]
  let finalize (sampled : F × F × Schnorr.ListROM.Shared.Tape F) (third : F × Schnorr.ListROM.Shared.Tape F) :=
    let signed := rawSign input.val.2.1.1.1 input.val.2.1.1.2 input.val.1 input.val.2.1.2.1 sampled.1 sampled.2.1 third.1
    (signed.1, (input.val.2.1.1, signed.2, input.val.2.1.2.2), third.2)
  calc Subtype.val <$> source config ops arith (PrivateSampler.Enumerated.Nonzero.bound_pos config.sampler) input
      = PrivateSampler.Pair.source config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler) trivial 1
            (Signing.Handler.tapes config.handler input) >>= fun sampled =>
          Schnorr.ListROM.Shared.tapeRun (Schnorr.liftRandom ((fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ : ProbComp Fˣ)))
            sampled.val.2.2 >>= fun third => pure (finalize sampled.val third) := by
        simp only [source, map_bind, map_pure]
        apply bind_congr_of_forall_mem_support
        intro sampled reached
        have drawn := nonce_source config _ (nonce_ready config input valid sampled reached)
        trans ((Subtype.val <$> PrivateSampler.Service.source config.handler.sampler
            (nonzeroCaller config (PrivateSampler.Enumerated.Nonzero.bound_pos config.sampler)) trivial 1
            (midValue config (sampled, Signing.Handler.context config.handler input)).1) >>= fun third =>
          pure (finalize sampled.val third))
        · rw [bind_map_left]
          congr 1
          funext nonce
          congr 1
          simp only [result, Signing.Handler.finishValue, workValue, midValue, Signing.Handler.context, value_eq]
          rfl
        · rw [drawn]
          rfl
    _ = (Subtype.val <$> PrivateSampler.Pair.source config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler)
            trivial 1 (Signing.Handler.tapes config.handler input)) >>= fun sampled =>
          Schnorr.ListROM.Shared.tapeRun (Schnorr.liftRandom ((fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ : ProbComp Fˣ)))
            sampled.2.2 >>= fun third => pure (finalize sampled third) := by
        rw [bind_map_left]
    _ = _ := by
        rw [pair_source config _ (pair_ready config input valid)]
        simp only [bind_assoc, bind_map_left]
        rfl

/-- The actual execution of the branch observes exactly the list backend's
nonzero signing oracle on the shared tape. -/
theorem observe_original (tape : RandomTape w) (input : config.handler.input.Value) (valid : ready config input)
    (before : State w) (holds : config.handler.input.representation.Holds input before) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    letI := PrivateSampler.Enumerated.Nonzero.unitsSampleable config.sampler
    (fun result => (Interactive.observe config.handler.output.representation result).map Subtype.val) <$>
      (code config ops arith (PrivateSampler.Enumerated.Nonzero.bound_pos config.sampler)).execute
        (Fresh.port config.handler.sampler.tape) .unit tape before =
      some <$> (Schnorr.ListROM.Shared.interpret
        (Schnorr.NonzeroListROM.handler (G₂ := G) (K := M) (.inr input.val.1))).run input.val.2 := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  let := PrivateSampler.Enumerated.Nonzero.unitsSampleable config.sampler
  have observed := (refines config ops arith (PrivateSampler.Enumerated.Nonzero.bound_pos config.sampler)).observe
    tape input valid before holds
  have mapped := congrArg (Functor.map (Option.map Subtype.val)) observed
  simp only [Functor.map_map, Option.map_some] at mapped
  have same := source_original config ops arith input valid
  simpa only [Functor.map_map, Option.map_some] using mapped.trans (by
    simpa only [Functor.map_map] using congrArg (Functor.map some) same)

end Main

end Signatures.Runtime.CaliperBackend.SchnorrROM.NonzeroSigning
