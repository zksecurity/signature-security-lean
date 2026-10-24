import Proofs.Runtime.BackendSchnorrROMHandlerComponents
import Proofs.Runtime.SchnorrROMSharedState

/-! Exact source correspondence for the actual shared-store routines.
Private sampler queries and attacker randomness share one raw uniform tape;
hash draws use the distinct challenge family. Every theorem includes both
caches, configuration and the entire saved/remaining tape. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeComponents

open BackendProgram RawTape

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (sample : sampler.denote () = ($ᵗ F : ProbComp F))

include sample

theorem challenge_source (tape : Shared.Tape F) :
    (NativeDraw.challenge rep data cost primitive sampler).denote ((), tape) =
      Shared.tapeRun (liftM ((expandedSpec F).query (.inr ()))) tape := by
  have h := NativeDraw.challenge_source rep data cost primitive sampler sample
    (⟨tape.1, tape.2⟩ : State F)
  simpa only [Shared.tapeRun, simulateQ_spec_query, NativeUniform.encodeState] using h

theorem hash_source (k : M × G₁) (saved : Shared.Store F G₁ M) :
    (hash rep data cost primitive sampler).denote (k, saved) =
      (Shared.interpret (handler (G₂ := G₂) (K := K) (.inl (.inr k)))).run saved := by
  rw [hash_denote, NativeCache.managed_denote, Shared.hash_run]
  cases hm : cacheMap saved.1.2.1 k with
  | some c => simp only [map_pure]
  | none =>
      rw [NativeCache.live_denote]
      cases hl : cacheMap saved.1.2.2 k with
      | some c => simp only [map_pure]
      | none =>
          simp only [challenge_source rep data cost primitive sampler sample, Functor.map_map]
          rfl

theorem finalHash_source (k : M × G₁) (saved : Shared.Store F G₁ M) :
    (finalHash rep data cost primitive sampler).denote (k, saved) =
      (Shared.interpret (ListROM.finalHash (G₂ := G₂) (K := K) k)).run saved := by
  rw [finalHash_denote, NativeCache.live_denote, Shared.finalHash_run]
  cases hl : cacheMap saved.1.2.2 k with
  | some c => simp only [map_pure]
  | none =>
      simp only [challenge_source rep data cost primitive sampler sample, Functor.map_map]
      rfl

omit sample in
theorem random_source (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
    (n : Nat) (saved : Shared.Store F G₁ M) :
    (fun p => (NativeUniform.decodeNat n p.1, p.2)) <$>
      (random rep data cost primitive uniform).denote (n, saved) =
        (Shared.interpret (handler (G₂ := G₂) (K := K) (.inl (.inl n)))).run saved := by
  rw [random_denote]
  have h := congrArg (Functor.map (fun p => (p.1, saved.1, p.2)))
    (NativePrivate.uniform_decoded rep data cost primitive uniform n
      (⟨saved.2.1, saved.2.2⟩ : State F))
  have hs : (Shared.interpret (handler (G₂ := G₂) (K := K) (.inl (.inl n)))).run saved =
      (fun p => (p.1, saved.1, p.2)) <$>
        Shared.tapeRun (liftM ((expandedSpec F).query (.inl n))) saved.2 := by
    change (fun p => (p.1.1, p.1.2, p.2)) <$>
      Shared.tapeRun ((fun r : Fin (n + 1) => (r, saved.1)) <$>
        (liftM ((expandedSpec F).query (.inl n)) : OracleComp (expandedSpec F) (Fin (n + 1)))) saved.2 = _
    rw [Shared.tapeRun_map, Functor.map_map]
    rfl
  rw [hs]
  simpa only [Shared.tapeRun, simulateQ_spec_query, NativeUniform.encodeState, Functor.map_map] using h

variable [Q.IsDistributive]
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (ports : NativePrivate.Ports (Q := Q) rep (iface := iface))

theorem private_source (tape : Shared.Tape F) :
    (NativePrivate.code rep data cost primitive uniform ports sampler).denote ((), tape) =
      Shared.tapeRun (privateImpl (.inr ())) tape := by
  exact NativePrivate.scalar_source rep data cost primitive uniform ports sampler sample
    (⟨tape.1, tape.2⟩ : State F)

theorem signing_source (msg : M) (saved : Shared.Store F G₁ M) :
    (signing rep data cost primitive uniform ports sampler).denote (msg, saved) =
      (Shared.interpret (handler (G₂ := G₂) (K := K) (.inr msg))).run saved := by
  rw [signing_denote, NativeCache.signing_denote, Shared.signing_run]
  simp only [private_source rep data cost primitive sampler sample uniform ports,
    map_bind, map_pure, Expr.run_value]
  rfl

end Signatures.Runtime.Schnorr.ListROM.NativeComponents
