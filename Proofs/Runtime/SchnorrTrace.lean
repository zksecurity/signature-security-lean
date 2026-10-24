import Proofs.Runtime.SchnorrSource

/-! The final live query and the native Fiat-Shamir trace. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

def nativeFinal (k : M × G₁) : StateT (NativeStore F G₁ M) (OracleComp (expandedSpec F)) F := fun s =>
  (fun p => (p.1, (s.1, s.2.1, p.2))) <$> (FiatShamir.Fork.roImpl M G₁ F k).run s.2.2

theorem expandedFinalHash_run (cost : PrimitiveCosts)
    (k : M × G₁) (g pk : G₁) (managed live : List ((M × G₁) × F)) :
    (expandState (taggedFinalHash.denote (arithmetic F G₁ G₂ K M cost) taggedSemantics (k, ()))).run
        ((g, pk), managed, live) =
      (fun p => (p.1, ((g, pk), managed, p.2))) <$>
        (cacheGetExpr hashEq LiveDraw.sample).denote (arithmetic F G₁ G₂ K M cost) liveDraw
          (k, 0, live, ()) := by
  change simulateQ (Replay.expandPrivate privateImpl)
    ((taggedFinalHash.denote (arithmetic F G₁ G₂ K M cost) taggedSemantics (k, ())).run
      ((g, pk), managed, live)) = _
  rw [taggedFinalHash_denote,
    cacheGetExpr_denote _ _ _ _ (hashEq_value (F := F) (G₂ := G₂) (K := K) cost), lookupValue_cacheMap]
  cases hc : cacheMap live k <;>
    simp [liveDraw, Replay.expandPrivate,
      FiatShamir.Fork.wrappedChallengeQuery, Functor.map_map]

theorem expandedFinalHash_refines (cost : PrimitiveCosts) (k : M × G₁) :
    StateRefines (nativeRepr (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M))
      (expandState (taggedFinalHash.denote (arithmetic F G₁ G₂ K M cost) taggedSemantics (k, ())))
      (nativeFinal k) := by
  rintro ⟨⟨g, pk⟩, managed, live⟩
  rw [expandedFinalHash_run]
  have h := liveGet_refines cost (liveDraw (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M))
    LiveDraw.sample rfl k 0 live
  have he := congrArg (fun main => (fun p : F × FiatShamir.Fork.SimState M G₁ F =>
      (p.1, ((g, pk), managedState managed, p.2))) <$> main) h
  change _ = (fun p => (p.1, ((g, pk), managedState managed, p.2))) <$>
    (FiatShamir.Fork.roImpl M G₁ F k).run (liveState live)
  simpa only [Functor.map_map, Function.comp_def, nativeRepr] using he

def nativePass (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) (M × G₁ × F)) :
    StateT (NativeStore F G₁ M) (OracleComp (expandedSpec F)) ((M × G₁ × F) × F) := do
  let forged ← simulateQ nativeImpl main
  let c ← nativeFinal (forged.1, forged.2.1)
  pure (forged, c)

theorem macroPass_refines (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    StateRefines (nativeRepr (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M))
      (expandState (macroPass cost randomBound code env))
      (nativePass (code.denote (arithmetic F G₁ G₂ K M cost) (sourceSemantics randomBound) env)) := by
  unfold macroPass nativePass
  simp only [expandState_bind, expandState_pure]
  apply StateRefines.bind nativeRepr (fun s => source_refines cost randomBound code env s)
  intro forged
  apply StateRefines.bind nativeRepr (expandedFinalHash_refines cost (forged.1, forged.2.1))
  intro c
  exact StateRefines.pure nativeRepr (forged, c)

omit [DecidableEq F] in
theorem nativePass_run (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) (M × G₁ × F))
    (g pk : G₁) (managed : (FiatShamir.fsRoSpec M G₁ F).QueryCache)
    (live : FiatShamir.Fork.SimState M G₁ F) :
    (nativePass main).run ((g, pk), managed, live) = (do
      let first ← (simulateQ liveImpl ((simulateQ (FiatShamir.simulatedNmaImpl (M := M)
        (_root_.Schnorr.simTranscript F G₁ g) pk) main).run managed)).run live
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

omit [Field F] [SampleableType F] [DecidableEq F] [AddCommGroup G₁] [Module F G₁] in
theorem roImpl_final {k : M × G₁} {live : FiatShamir.Fork.SimState M G₁ F}
    {out : F × FiatShamir.Fork.SimState M G₁ F}
    (h : out ∈ support ((FiatShamir.Fork.roImpl M G₁ F k).run live)) : out.2.1 k = some out.1 := by
  rcases live with ⟨cache, log⟩
  cases hc : cache k with
  | some c =>
    rw [FiatShamir.Fork.roImpl_run_some (M := M) (Commit := G₁) (Chal := F) k cache log c hc] at h
    simp only [support_pure, Set.mem_singleton_iff] at h
    subst out
    exact hc
  | none =>
    rw [FiatShamir.Fork.roImpl_run_none (M := M) (Commit := G₁) (Chal := F) k cache log hc] at h
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨c, _, rfl⟩ := h
    exact QueryCache.cacheQuery_self _ _ _

def nativeTrace (p : ((M × G₁ × F) × F) × NativeStore F G₁ M) :
    FiatShamir.Fork.Trace G₁ F F M where
  forgery := p.1.1
  advCache := p.2.2.1
  roCache := p.2.2.2.1
  queryLog := p.2.2.2.2
  verified := decide (p.1.1.2.2 • p.2.1.1 = p.1.1.2.1 + p.1.2 • p.2.1.2)

def cacheTrace (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) :
    FiatShamir.Fork.Trace G₁ F F M := nativeTrace (p.1, nativeRepr p.2)

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

theorem macroPass_valid (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (g pk : G₁)
    (managed live : List ((M × G₁) × F))
    (out : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (h : out ∈ support (simulateQ (Replay.expandPrivate privateImpl)
      ((macroPass cost randomBound code env).run ((g, pk), managed, live)))) :
    out.2.1 = (g, pk) ∧ (listQueryCache out.2.2.2) (out.1.1.1, out.1.1.2.1) = some out.1.2 := by
  have href := macroPass_refines cost randomBound code env ((g, pk), managed, live)
  dsimp only [nativeRepr] at href
  have hs : (out.1, nativeRepr out.2) ∈ support
      ((nativePass (code.denote (arithmetic F G₁ G₂ K M cost) (sourceSemantics randomBound) env)).run
        ((g, pk), managedState managed, liveState live)) := by
    rw [← href]
    rw [support_map]
    exact ⟨out, h, rfl⟩
  exact nativePass_valid _ g pk (managedState managed) (liveState live) _ hs

variable [SampleableType G₁]

omit [DecidableEq F] in
theorem nativePass_trace (g pk : G₁) (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g) :
    nativeTrace <$> (nativePass (adv.main pk)).run ((g, pk), ∅, (∅, [])) =
      FiatShamir.Fork.runTrace (_root_.Schnorr.sigma F G₁ g) (DiffieHellman.dlogGenerable F g) M
        (FiatShamir.cmaToNmaAdv (_root_.Schnorr.sigma F G₁ g) (DiffieHellman.dlogGenerable F g) M
          (_root_.Schnorr.simTranscript F G₁ g) adv) pk := by
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
  simp only [nativeTrace, hc, _root_.Schnorr.sigma]

theorem SourceCertificate.trace (cost : PrimitiveCosts) (randomBound localTime : Nat)
    (queries : Fin 3 → Nat) (g : G₁) (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g)
    (cert : SourceCertificate (G₂ := G₂) (K := K) cost randomBound localTime queries adv.main) (pk : G₁) :
    cacheTrace <$> simulateQ (Replay.expandPrivate privateImpl)
      ((macroPass cost randomBound cert.code (pk, cert.data, ())).run ((g, pk), [], [])) =
      FiatShamir.Fork.runTrace (_root_.Schnorr.sigma F G₁ g) (DiffieHellman.dlogGenerable F g) M
        (FiatShamir.cmaToNmaAdv (_root_.Schnorr.sigma F G₁ g) (DiffieHellman.dlogGenerable F g) M
          (_root_.Schnorr.simTranscript F G₁ g) adv) pk := by
  have h := macroPass_refines cost randomBound cert.code (pk, cert.data, ()) ((g, pk), [], [])
  rw [cert.semantics] at h
  have he := congrArg (Functor.map nativeTrace) h
  have hempty : nativeRepr (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
      ((g, pk), [], []) = ((g, pk), ∅, (∅, [])) := by
    have hm : managedState ([] : List ((M × G₁) × F)) = ∅ := by
      apply QueryCache.ext
      intro i
      cases i <;> rfl
    have hl : liveState ([] : List ((M × G₁) × F)) = (∅, []) := by
      apply Prod.ext
      · apply QueryCache.ext
        intro i
        rfl
      · rfl
    exact Prod.ext rfl (Prod.ext hm hl)
  rw [hempty] at he
  calc
    _ = nativeTrace <$> (nativePass (adv.main pk)).run ((g, pk), ∅, (∅, [])) := by
      unfold cacheTrace
      simpa only [Functor.map_map, cacheTrace, expandState, StateT.run] using he
    _ = _ := nativePass_trace g pk adv

end Signatures.Runtime.Schnorr
