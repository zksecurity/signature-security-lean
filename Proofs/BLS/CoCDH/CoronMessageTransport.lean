import Proofs.BLS.CoCDH.MessageTransport
import Proofs.BLS.CoCDH.CacheTransport
import Proofs.Runtime.CoronErasure

/-! Exact injective-message transport for the two lazy Coron caches and the
complete named solver. The existing flattened semantics is used only to prove
equality; no new solver implementation or runtime cost is assumed. -/

open BLS.ROM

open OracleComp OracleSpec BLS.CoCDH.Tight Signatures.Runtime.Coron

namespace BLS.CoCDH.MessageTransport

variable {N M : Type} (f : N → M)
variable [DecidableEq N] [DecidableEq M] (hf : Function.Injective f)

include hf

variable {F G₁ : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁]

noncomputable def projectNativeState {qS : Nat} (st : NativeState F M qS) : NativeState F N qS :=
  (projectState f hf st.1, projectCache f st.2)

omit [DecidableEq N] [DecidableEq M] [Field F] [SampleableType F] in
@[simp] theorem projectNativeState_empty (qS : Nat) :
    projectNativeState (F := F) f hf (qS := qS) ((fun _ => none, ∅), ∅) =
      ((fun _ => none, ∅), ∅) := by simp [projectNativeState]

theorem nativeReply_project (g X h : G₁) (qS : Nat) (signing : Bool) (n : N)
    (st : NativeState F M qS) :
    Prod.map id (projectNativeState f hf) <$> (nativeReply g X h qS signing (f n)).run st =
      (nativeReply g X h qS signing n).run (projectNativeState f hf st) := by
  have hmark : projectState f hf (st.1.1, if signing then insert (f n) st.1.2 else st.1.2) =
      ((projectState f hf st.1).1, if signing then insert n (projectState f hf st.1).2
        else (projectState f hf st.1).2) := by
    cases signing
    · rfl
    · exact projectState_insert f hf st.1 n
  simp only [nativeReply_run, projectNativeState, map_bind]
  rw [← hmark, ← getDlogS_project f hf n (st.1.1, if signing then insert (f n) st.1.2 else st.1.2),
    bind_map_left]
  apply bind_congr
  intro rho
  rw [← randomOracle_project f hf st.2 n, bind_map_left]
  simp [projectNativeState]

theorem nativeOracle_project (g X h : G₁) (qS : Nat) (q : (advSpec N G₁).Domain)
    (st : NativeState F M qS) :
    Prod.map id (projectNativeState f hf) <$>
      (simulateQ (nativeOracle (F := F) g X h qS) (messageQueries f q)).run st =
      (nativeOracle (F := F) g X h qS q).run (projectNativeState f hf st) := by
  rcases q with ((n | n) | n)
  · simp [messageQueries, nativeOracle, StateT.run, Functor.map_map]
  · simpa only [messageQueries, simulateQ_HasQuery_query, nativeOracle] using
      nativeReply_project f hf g X h qS false n st
  · simpa only [messageQueries, simulateQ_HasQuery_query, nativeOracle] using
      nativeReply_project f hf g X h qS true n st

theorem nativeReduction_mapMessages (g X h : G₁) (qS : Nat) (adv : Adversary N G₁) :
    nativeReduction (F := F) g X h qS (mapMessages f adv) =
      nativeReduction (F := F) g X h qS adv := by
  rw [nativeReduction_cached, nativeReduction_cached, ← mapMessages_cacheForgery]
  have hs := run_messageQueries_project f (nativeOracle (F := F) g X h qS)
    (nativeOracle (F := F) g X h qS) (projectNativeState f hf)
    (nativeOracle_project f hf g X h qS) (cacheForgery adv) ((fun _ => none, ∅), ∅)
  rw [projectNativeState_empty] at hs
  simp only [mapMessages, simulateQ_map, StateT.run_map, Functor.map_map]
  rw [← hs, Functor.map_map]
  rfl

theorem coronReductionLazyPK_mapMessages {G₂ : Type} (g X h : G₁) (g₂ pk : G₂) (qS : Nat)
    (adv : AdversaryPK N G₁ G₂) :
    coronReductionLazyPK (F := F) qS (cacheForgeryPK (fun key => mapMessages f (adv key))) g g₂ X pk h =
      coronReductionLazyPK (F := F) qS (cacheForgeryPK adv) g g₂ X pk h := by
  rw [← nativeReduction_original, ← nativeReduction_original]
  exact nativeReduction_mapMessages f hf g X h qS (adv pk)

omit hf [DecidableEq N] in
theorem coronReductionLazyPK_congr_at {G₂ : Type} (g X h : G₁) (g₂ pk : G₂) (qS : Nat)
    (adv adv' : AdversaryPK M G₁ G₂) (hkey : adv pk = adv' pk) :
    coronReductionLazyPK (F := F) qS (cacheForgeryPK adv) g g₂ X pk h =
      coronReductionLazyPK (F := F) qS (cacheForgeryPK adv') g g₂ X pk h := by
  rw [← nativeReduction_original, ← nativeReduction_original, hkey]

variable {G₂ : Type} [AddCommGroup G₂] [Module F G₂] [SampleableType G₁]

omit hf [DecidableEq N] in
theorem coCDHExp_coron_congr_generated (g : G₁) (g₂ : G₂) (qS : Nat)
    (adv adv' : AdversaryPK M G₁ G₂) (hkey : ∀ r : F, adv (r • g₂) = adv' (r • g₂)) :
    coCDHExp (F := F) g g₂ (coronReductionLazyPK (F := F) qS (cacheForgeryPK adv)) =
      coCDHExp (F := F) g g₂ (coronReductionLazyPK (F := F) qS (cacheForgeryPK adv')) := by
  unfold coCDHExp
  apply bind_congr
  intro r
  apply bind_congr
  intro h
  rw [coronReductionLazyPK_congr_at g (r • g) h g₂ (r • g₂) qS adv adv' (hkey r)]

theorem coCDHExp_coron_mapMessages (g : G₁) (g₂ : G₂) (qS : Nat) (adv : AdversaryPK N G₁ G₂) :
    coCDHExp (F := F) g g₂
        (coronReductionLazyPK (F := F) qS (cacheForgeryPK (fun pk => mapMessages f (adv pk)))) =
      coCDHExp (F := F) g g₂ (coronReductionLazyPK (F := F) qS (cacheForgeryPK adv)) := by
  unfold coCDHExp
  apply bind_congr
  intro r
  apply bind_congr
  intro h
  rw [coronReductionLazyPK_mapMessages f hf g (r • g) h g₂ (r • g₂) qS adv]

end BLS.CoCDH.MessageTransport
