import Proofs.Runtime.SchnorrROMListPass
import Proofs.Runtime.BackendSchnorrNonzeroSigningSource
import Proofs.Schnorr.NonzeroLazyROMReduction

/-! Finite-cache execution of the nonzero-nonce simulator for arbitrary adaptive
attackers. The proof-side cache functions are only a representation map. The
implemented pass stores encountered entries and keeps managed/live caches apart. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.NonzeroListROM

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [SampleableType Fˣ] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

def nativeImpl : QueryImpl (FiatShamir.cmaOracleSpec M G₁ F F)
    (StateT (NativeStore F G₁ M) (OracleComp (expandedSpec F))) := fun i s =>
  (fun p => (p.1.1, (s.1, p.1.2, p.2))) <$>
    (simulateQ liveImpl ((FiatShamir.simulatedNmaImpl (M := M)
      (_root_.Schnorr.NonzeroNonce.simTranscript s.1.1) s.1.2 i).run s.2.1)).run s.2.2

omit [DecidableEq F] in
theorem nativeImpl_run {A : Type}
    (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) A)
    (g pk : G₁) (managed : (FiatShamir.fsRoSpec M G₁ F).QueryCache)
    (live : FiatShamir.Fork.SimState M G₁ F) :
    (simulateQ nativeImpl main).run ((g, pk), managed, live) =
      (fun p => (p.1.1, ((g, pk), p.1.2, p.2))) <$>
        (simulateQ liveImpl ((simulateQ (FiatShamir.simulatedNmaImpl (M := M)
          (_root_.Schnorr.NonzeroNonce.simTranscript g) pk) main).run managed)).run live := by
  induction main using OracleComp.inductionOn generalizing managed live with
  | pure a => simp
  | query_bind i next ih =>
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, map_bind]
    dsimp only [nativeImpl, StateT.run]
    simp only [bind_map_left]
    congr 1
    funext p
    exact ih p.1.1 p.1.2 p.2

omit [DecidableEq F] in
theorem nativeImpl_sign (msg : M) (g pk : G₁)
    (managed : (FiatShamir.fsRoSpec M G₁ F).QueryCache) (live : FiatShamir.Fork.SimState M G₁ F) :
    (nativeImpl (.inr msg)).run ((g, pk), managed, live) =
      (fun t : G₁ × F × F => ((t.1, t.2.2), ((g, pk),
        (match managed (.inr (msg, t.1)) with
        | some _ => managed
        | none => managed.cacheQuery (.inr (msg, t.1)) t.2.1), live))) <$>
        liftRandom (_root_.Schnorr.NonzeroNonce.simTranscript g pk) := by
  change (fun p => (p.1.1, ((g, pk), p.1.2, p.2))) <$>
    (simulateQ liveImpl ((FiatShamir.simulatedNmaSigSim (M := M)
      (_root_.Schnorr.NonzeroNonce.simTranscript g) pk msg).run managed)).run live = _
  simp only [FiatShamir.simulatedNmaSigSim, StateT.run_bind, unifSim_run,
    StateT.run_modifyGet, bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
  rw [liveImpl_uniform]
  simp only [Functor.map_map]
  congr 1
  funext t
  cases managed (.inr (msg, t.1)) <;> rfl

/-- The signer uses the repaired transcript and only updates the managed cache.
Private sampling remains on the original dynamic uniform interface. -/
def handler : QueryImpl (FiatShamir.cmaOracleSpec M G₁ F F)
    (StateT (cacheStore.Value (cryptoBase F G₁ G₂ K M)) (OracleComp (expandedSpec F)))
  | .inl i => ListROM.handler (.inl i)
  | .inr msg => fun s =>
      (fun p => (p.1, (s.1, p.2, s.2.2))) <$>
        liftRandom (NonzeroSigning.source s.1.1 s.1.2 msg s.2.1)

theorem handler_refines (i : (Nat ⊕ (M × G₁)) ⊕ M) :
    StateRefines (nativeRepr (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M))
      (handler i) (nativeImpl i) := by
  rcases i with (n | k) | msg
  · exact ListROM.handler_refines (.inl (.inl n))
  · exact ListROM.handler_refines (.inl (.inr k))
  · rintro ⟨⟨g, pk⟩, managed, live⟩
    change (fun p => (p.1, nativeRepr p.2)) <$>
      ((fun p => (p.1, ((g, pk), p.2, live))) <$>
        liftRandom (NonzeroSigning.source g pk msg managed)) =
      (nativeImpl (.inr msg)).run ((g, pk), managedState managed, liveState live)
    rw [nativeImpl_sign]
    simp only [NonzeroSigning.source, liftRandom, bind_pure_comp, simulateQ_map, Functor.map_map]
    congr 1
    funext t
    have hp := cacheProgram_managedState (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
      PrimitiveCosts.unit (msg, t.1) t.2.1 managed
    rw [Expr.run_value, ListROM.NativeCache.programming_value] at hp
    change ((t.1, t.2.2), ((g, pk), managedState (CacheProgramming.value (msg, t.1) t.2.1 managed),
      liveState live)) = _
    rw [hp]
    cases managedState managed (.inr (msg, t.1)) <;> rfl

def nativePass (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) (M × G₁ × F)) :
    StateT (NativeStore F G₁ M) (OracleComp (expandedSpec F)) ((M × G₁ × F) × F) := do
  let forged ← simulateQ nativeImpl main
  let c ← nativeFinal (forged.1, forged.2.1)
  pure (forged, c)

omit [DecidableEq F] in
theorem nativePass_run (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) (M × G₁ × F))
    (g pk : G₁) (managed : (FiatShamir.fsRoSpec M G₁ F).QueryCache)
    (live : FiatShamir.Fork.SimState M G₁ F) :
    (nativePass main).run ((g, pk), managed, live) = (do
      let first ← (simulateQ liveImpl ((simulateQ (FiatShamir.simulatedNmaImpl (M := M)
        (_root_.Schnorr.NonzeroNonce.simTranscript g) pk) main).run managed)).run live
      let last ← (FiatShamir.Fork.roImpl M G₁ F (first.1.1.1, first.1.1.2.1)).run first.2
      pure ((first.1.1, last.1), ((g, pk), first.1.2, last.2))) := by
  simp only [nativePass, StateT.run_bind, nativeImpl_run, bind_map_left,
    bind_pure_comp]
  congr 1
  funext first
  rw [StateT.run_map]
  change (fun p => ((first.1.1, p.1), p.2)) <$>
    ((fun p => (p.1, ((g, pk), first.1.2, p.2))) <$>
      (FiatShamir.Fork.roImpl M G₁ F (first.1.1.1, first.1.1.2.1)).run first.2) = _
  simp only [Functor.map_map]

omit [DecidableEq F] in
theorem nativePass_valid (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) (M × G₁ × F))
    (g pk : G₁) (managed : (FiatShamir.fsRoSpec M G₁ F).QueryCache)
    (live : FiatShamir.Fork.SimState M G₁ F)
    (out : ((M × G₁ × F) × F) × NativeStore F G₁ M)
    (h : out ∈ support ((nativePass main).run ((g, pk), managed, live))) :
    out.2.1 = (g, pk) ∧ out.2.2.2.1 (out.1.1.1, out.1.1.2.1) = some out.1.2 := by
  rw [nativePass_run] at h
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
  obtain ⟨first, _, last, hl, rfl⟩ := h
  exact ⟨rfl, roImpl_final hl⟩

def pass (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) (M × G₁ × F)) :
    StateT (cacheStore.Value (cryptoBase F G₁ G₂ K M)) (OracleComp (expandedSpec F))
      ((M × G₁ × F) × F) := do
  let forged ← simulateQ handler main
  let c ← ListROM.finalHash (forged.1, forged.2.1)
  pure (forged, c)

/-- Exact adaptive output/state correspondence for the nonzero simulator. -/
theorem pass_refines (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) (M × G₁ × F)) :
    StateRefines (nativeRepr (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M))
      (pass main) (nativePass main) := by
  unfold pass nativePass
  apply StateRefines.bind (nativeRepr (G₂ := G₂) (K := K))
    (GeneralCaller.simulateQ_refines (nativeRepr (G₂ := G₂) (K := K)) handler nativeImpl
      (handler_refines (G₂ := G₂) (K := K)) main)
  intro forged
  apply StateRefines.bind (nativeRepr (G₂ := G₂) (K := K))
    (expandedFinalHash_refines (G₂ := G₂) (K := K) PrimitiveCosts.unit _)
  intro c
  exact StateRefines.pure (nativeRepr (G₂ := G₂) (K := K)) (forged, c)

/-- The finite output retains the challenge obtained by the final live query. -/
theorem pass_valid (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) (M × G₁ × F))
    (g pk : G₁) (managed live : List ((M × G₁) × F))
    (out : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (h : out ∈ support ((pass main).run ((g, pk), managed, live))) :
    out.2.1 = (g, pk) ∧ (listQueryCache out.2.2.2) (out.1.1.1, out.1.1.2.1) = some out.1.2 := by
  have hs : (out.1, nativeRepr (G₂ := G₂) (K := K) out.2) ∈ support
      ((nativePass main).run (nativeRepr (G₂ := G₂) (K := K) ((g, pk), managed, live))) := by
    rw [← pass_refines (G₂ := G₂) (K := K) main ((g, pk), managed, live), support_map]
    exact ⟨out, h, rfl⟩
  exact nativePass_valid main g pk (managedState managed) (liveState live) _ hs

variable [SampleableType G₁]

omit [DecidableEq F] in
theorem nativePass_trace (g pk : G₁) (adv : _root_.Schnorr.NonzeroNonce.Adversary (F := F) (M := M) g) :
    nativeTrace <$> (nativePass (adv.main pk)).run ((g, pk), ∅, (∅, [])) =
      FiatShamir.Fork.runTrace (_root_.Schnorr.NonzeroNonce.sigma g) (DiffieHellman.dlogGenerable F g) M
        (FiatShamir.cmaToNmaAdv (_root_.Schnorr.NonzeroNonce.sigma g) (DiffieHellman.dlogGenerable F g) M
          (_root_.Schnorr.NonzeroNonce.simTranscript g) adv) pk := by
  rw [nativePass_run]
  simp only [map_bind, map_pure]
  unfold FiatShamir.Fork.runTrace FiatShamir.cmaToNmaAdv
    FiatShamir.Stateful.nmaAdvFromCmaWithFinalQuery FiatShamir.Stateful.nmaAdvFromCma
    FiatShamir.simulatedNmaAdv
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    pure_bind, simulateQ_spec_query, bind_assoc]
  congr 1
  funext first
  apply bind_congr_of_forall_mem_support
  intro last hl
  have hc := roImpl_final hl
  simp only [nativeTrace, hc, _root_.Schnorr.NonzeroNonce.sigma, _root_.Schnorr.sigma]

/-- Exact computation equality to the pass used in the established ROM proof,
including both caches, chronological live queries and verification. -/
theorem pass_trace (g pk : G₁) (adv : _root_.Schnorr.NonzeroNonce.Adversary (F := F) (M := M) g) :
    cacheTrace <$> (pass (G₂ := G₂) (K := K) (adv.main pk)).run ((g, pk), [], []) =
      _root_.Schnorr.NonzeroNonce.LazyROM.main g pk adv := by
  have he := congrArg (Functor.map nativeTrace)
    (pass_refines (G₂ := G₂) (K := K) (adv.main pk) ((g, pk), [], []))
  rw [ListROM.empty_repr] at he
  calc
    _ = nativeTrace <$> (nativePass (adv.main pk)).run ((g, pk), ∅, (∅, [])) := by
      unfold cacheTrace
      simpa only [Functor.map_map, cacheTrace] using he
    _ = _ := nativePass_trace g pk adv

end Signatures.Runtime.Schnorr.NonzeroListROM
