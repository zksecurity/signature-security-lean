import Proofs.Runtime.SchnorrTrace
import Proofs.Runtime.GeneralCallerRefinement
import Proofs.Schnorr.LazyROMReduction

/-! The finite-list Schnorr ROM pass for an arbitrary adversary computation.
Only the reduction's cache routines use the arithmetic language. Attacker
randomness has the original dynamic uniform interface, with no arity bound or
source-language certificate. Managed and live caches remain separate, and the
last verification query always uses the live cache. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.ListROM

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

/-- The original CMA interface, interpreted using only encountered cache entries.
The fixed zero in the hash/sign routines does not bound any attacker randomness;
neither routine has a `Command.random` constructor. -/
def handler : QueryImpl (FiatShamir.cmaOracleSpec M G₁ F F)
    (StateT (cacheStore.Value (cryptoBase F G₁ G₂ K M)) (OracleComp (expandedSpec F)))
  | .inl (.inl n) => fun s =>
      (fun r => (r, s)) <$> (liftM ((expandedSpec F).query (.inl n)) : OracleComp _ (Fin (n + 1)))
  | .inl (.inr k) => expandedSource PrimitiveCosts.unit 0 .hash k
  | .inr msg => expandedSource PrimitiveCosts.unit 0 .sign msg

theorem handler_refines (i : (Nat ⊕ (M × G₁)) ⊕ M) :
    StateRefines (nativeRepr (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M))
      (handler i) (nativeImpl i) := by
  rcases i with (n | k) | msg
  · intro s
    rcases s with ⟨⟨g, pk⟩, managed, live⟩
    have h := expandedSource_random_refines (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
      PrimitiveCosts.unit n ⟨n, Nat.lt_succ_self n⟩ ((g, pk), managed, live)
    simpa only [expandedSource, expandState, taggedRoutines, Program.denote,
      taggedSemantics, StateT.run, simulateQ_map, simulateQ_spec_query,
      Replay.expandPrivate, privateImpl, Functor.map_map, handler,
      boundedNat, Ty.Value, cryptoBase, OracleSpec.Range, FiatShamir.cmaOracleSpec,
      FiatShamir.fsRoSpec, OracleSpec.add_apply_inl, unifSpec, OracleSpec.ofFn] using h
  · exact expandedSource_hash_refines (G₂ := G₂) (K := K) PrimitiveCosts.unit 0 k
  · exact expandedSource_sign_refines (G₂ := G₂) (K := K) PrimitiveCosts.unit 0 msg

def finalHash (k : M × G₁) :
    StateT (cacheStore.Value (cryptoBase F G₁ G₂ K M)) (OracleComp (expandedSpec F)) F :=
  expandState (taggedFinalHash.denote (arithmetic F G₁ G₂ K M PrimitiveCosts.unit)
    taggedSemantics (k, ()))

def pass (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) (M × G₁ × F)) :
    StateT (cacheStore.Value (cryptoBase F G₁ G₂ K M)) (OracleComp (expandedSpec F))
      ((M × G₁ × F) × F) := do
  let forged ← simulateQ handler main
  let c ← finalHash (forged.1, forged.2.1)
  pure (forged, c)

/-- Full adaptive answer/state correspondence; no attacker implementation
language is assumed. -/
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

omit [Field F] [SampleableType F] [DecidableEq F] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] in
theorem empty_repr (g pk : G₁) :
    nativeRepr (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) ((g, pk), [], []) =
      ((g, pk), ∅, (∅, [])) := by
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

/-- Exact computation equality to the pass used in the established ROM proof,
including both caches, chronological live queries and verification. -/
theorem pass_trace (g pk : G₁) (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g) :
    cacheTrace <$> (pass (G₂ := G₂) (K := K) (adv.main pk)).run ((g, pk), [], []) =
      _root_.Schnorr.LazyROM.main g pk adv := by
  have he := congrArg (Functor.map nativeTrace)
    (pass_refines (G₂ := G₂) (K := K) (adv.main pk) ((g, pk), [], []))
  rw [empty_repr] at he
  calc
    _ = nativeTrace <$> (nativePass (adv.main pk)).run ((g, pk), ∅, (∅, [])) := by
      unfold cacheTrace
      simpa only [Functor.map_map, cacheTrace] using he
    _ = _ := nativePass_trace g pk adv

end Signatures.Runtime.Schnorr.ListROM
