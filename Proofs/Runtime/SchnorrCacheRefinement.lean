import Proofs.Runtime.SchnorrCache
import Proofs.Runtime.CacheRefinement
import VCVio.CryptoFoundations.FiatShamir.Sigma.CmaToNma

/-! Representation bridges from executed association-list caches to the managed and
live caches in VCVio's Fiat-Shamir reduction. These maps are proof-only abstractions. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr

variable {F G₁ G₂ K M : Type} [Field F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

/-- Prepending cache misses implements an append-only chronological live query log. -/
def liveState (xs : List ((M × G₁) × F)) : FiatShamir.Fork.SimState M G₁ F :=
  (listQueryCache xs, xs.reverse.map Prod.fst)

variable {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}

theorem liveGet_refines (cost : PrimitiveCosts)
    (H : Semantics (cryptoBase F G₁ G₂ K M) Cmd (FiatShamir.Fork.wrappedSpec F))
    (draw : Cmd .unit scalar)
    (hdraw : H draw () = FiatShamir.Fork.wrappedChallengeQuery F)
    (k : M × G₁) (default : F) (xs : List ((M × G₁) × F)) :
    (fun p => (p.1, liveState p.2)) <$>
        (cacheGetExpr hashEq draw).denote (arithmetic F G₁ G₂ K M cost) H (k, default, xs, ()) =
      (FiatShamir.Fork.roImpl M G₁ F k).run (liveState xs) := by
  rw [cacheGetExpr_denote _ _ _ _ (hashEq_value (F := F) (G₂ := G₂) (K := K) cost)]
  rw [lookupValue_cacheMap]
  cases hc : cacheMap xs k with
  | some v =>
    have hx : listQueryCache xs k = some v := hc
    simp [liveState, FiatShamir.Fork.roImpl_run_some M _ _ _ _ hx]
  | none =>
    have hx : listQueryCache xs k = none := hc
    simp [liveState, FiatShamir.Fork.roImpl_run_none M _ _ _ hx,
      hdraw, Functor.map_map, bind_pure_comp, listQueryCache_cons]

def managedState (xs : List ((M × G₁) × F)) : (FiatShamir.fsRoSpec M G₁ F).QueryCache :=
  .ofFn (fun i => match i with
    | .inl _ => none
    | .inr k => cacheMap xs k)

omit [Field F] [DecidableEq F] [AddCommGroup G₁] [Module F G₁] in
theorem managedState_cons (k : M × G₁) (v : F) (xs : List ((M × G₁) × F)) :
    managedState ((k, v) :: xs) = (managedState xs).cacheQuery (.inr k) v := by
  apply QueryCache.ext
  intro i
  cases i with
  | inl n => simp [managedState]
  | inr k' =>
    by_cases h : k = k'
    · subst k'; simp [managedState, cacheMap]
    · simp [managedState, cacheMap, h, Ne.symm h]

/-- Programming an existing entry preserves it, exactly as `simulatedNmaSigSim` does. -/
theorem cacheProgram_managedState (cost : PrimitiveCosts)
    (k : M × G₁) (v : F) (xs : List ((M × G₁) × F)) :
    managedState ((cacheProgram (val := scalar) hashEq).run (arithmetic F G₁ G₂ K M cost) (k, v, xs, ())).value =
      match managedState xs (.inr k) with
      | some _ => managedState xs
      | none => (managedState xs).cacheQuery (.inr k) v := by
  rw [cacheProgram_value _ _ (hashEq_value (F := F) (G₂ := G₂) (K := K) cost)]
  rw [lookupValue_cacheMap]
  have hx : managedState xs (.inr k) = cacheMap xs k := by
    simp [managedState]
  rw [hx]
  cases cacheMap xs k <;> simp [managedState_cons]

theorem managedGet_refines (cost : PrimitiveCosts)
    (H : Semantics (cryptoBase F G₁ G₂ K M) Cmd (FiatShamir.Fork.wrappedSpec F))
    (draw : Cmd .unit scalar)
    (hdraw : H draw () = FiatShamir.Fork.wrappedChallengeQuery F)
    (k : M × G₁) (default : F) (managed live : List ((M × G₁) × F)) :
    (fun p => ((p.1, managedState p.2.1), liveState p.2.2)) <$>
        (managedGet draw).denote (arithmetic F G₁ G₂ K M cost) H
          (k, default, managed, live, ()) =
      (simulateQ (FiatShamir.Fork.unifForward M G₁ F + FiatShamir.Fork.roImpl M G₁ F)
        ((FiatShamir.simulatedNmaRoSim (M := M) (Commit := G₁) (Chal := F) k).run
          (managedState managed))).run (liveState live) := by
  rw [managedGet_denote, lookupValue_cacheMap]
  have hm : managedState managed (.inr k) = cacheMap managed k := by simp [managedState]
  simp only [FiatShamir.simulatedNmaRoSim, StateT.run_bind, StateT.run_get, pure_bind, hm]
  cases hc : cacheMap managed k with
  | some v => simp
  | none =>
    have hf : (FiatShamir.simulatedNmaFwd (M := M) (Commit := G₁) (Chal := F)
        (.inr k)).run (managedState managed) =
        (fun v : F => (v, managedState managed)) <$>
          (liftM ((FiatShamir.fsRoSpec M G₁ F).query (.inr k)) :
            OracleComp (FiatShamir.fsRoSpec M G₁ F) F) := by
      rfl
    simp only [Bool.false_eq_true, ite_false, Functor.map_map,
      StateT.run_bind, StateT.run_modifyGet, hf, bind_pure_comp]
    have hl := liveGet_refines cost H draw hdraw k default live
    have hmap := congrArg (Functor.map (fun p : F × FiatShamir.Fork.SimState M G₁ F =>
      ((p.1, (managedState managed).cacheQuery (.inr k) p.1), p.2))) hl
    simpa [simulateQ_map, simulateQ_query, QueryImpl.add, StateT.run_map,
      Functor.map_map, managedState_cons] using hmap

def uniformToRo : QueryImpl unifSpec (OracleComp (FiatShamir.fsRoSpec M G₁ F)) :=
  fun n => liftM ((FiatShamir.fsRoSpec M G₁ F).query (.inl n))

omit [Field F] [DecidableEq F] [AddCommGroup G₁] [Module F G₁] in
theorem unifSim_run {A : Type} (oa : ProbComp A)
    (s : (FiatShamir.fsRoSpec M G₁ F).QueryCache) :
    (simulateQ (FiatShamir.simulatedNmaUnifSim (M := M) (Commit := G₁) (Chal := F)) oa).run s =
      (fun x => (x, s)) <$> simulateQ uniformToRo oa := by
  have h : FiatShamir.simulatedNmaUnifSim (M := M) (Commit := G₁) (Chal := F) =
      (uniformToRo (F := F) (G₁ := G₁) (M := M)).liftTarget
        (StateT (FiatShamir.fsRoSpec M G₁ F).QueryCache
          (OracleComp (FiatShamir.fsRoSpec M G₁ F))) := by
    funext n
    rfl
  rw [h, simulateQ_liftTarget]
  simp only [StateT.run_liftM, bind_pure_comp]

variable [SampleableType F]

/-- Both simulated scalars are ordinary private randomness, not live hash queries.
The exact bridge retains a pre-existing programmed challenge on collision. -/
theorem signCached_refines (cost : PrimitiveCosts)
    (H : Semantics (cryptoBase F G₁ G₂ K M) Cmd (FiatShamir.fsRoSpec M G₁ F))
    (draw : Cmd .unit scalar)
    (hdraw : H draw () = simulateQ uniformToRo ($ᵗ F : ProbComp F))
    (msg : M) (g pk : G₁) (managed : List ((M × G₁) × F)) :
    (fun p => (p.1, managedState p.2)) <$>
        (signCached draw).denote (arithmetic F G₁ G₂ K M cost) H (msg, g, pk, managed, ()) =
      (FiatShamir.simulatedNmaSigSim (M := M) (_root_.Schnorr.simTranscript F G₁ g) pk msg).run
        (managedState managed) := by
  rw [signCached_denote]
  simp only [map_bind, map_pure]
  simp only [FiatShamir.simulatedNmaSigSim, StateT.run_bind, StateT.run_modifyGet,
    unifSim_run, _root_.Schnorr.simTranscript, simulateQ_bind, simulateQ_pure,
    bind_map_left, bind_assoc, pure_bind, hdraw]
  congr 1
  funext c
  congr 1
  funext z
  rw [cacheProgram_managedState (F := F) (G₂ := G₂) (K := K) cost]
  cases managedState managed (.inr (msg, z • g - c • pk)) <;> rfl

end Signatures.Runtime.Schnorr
