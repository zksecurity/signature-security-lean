import Signatures.Runtime.SchnorrSeedBudget
import Signatures.Runtime.PathCost

/-! The typed simulation's live cache records exactly its forkable queries.
This proves selector reachability before expanding any private scalar sampler. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr

def liveWeight : (Nat ⊕ Unit) ⊕ Unit → Nat := fun i => if i = .inr () then 1 else 0

def liveLength {F G₁ G₂ K M : Type}
    (state : cacheStore.Value (cryptoBase F G₁ G₂ K M)) : Nat := state.2.2.length

variable {F G₁ G₂ K M : Type} [Field F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem taggedSign_liveLength (cost : PrimitiveCosts) (msg : M) (g pk : G₁)
    (managed live : List ((M × G₁) × F)) (out) (n : Nat)
    (h : QueryCost liveWeight ((taggedSign.denote (arithmetic F G₁ G₂ K M cost)
      taggedSemantics (msg, ())).run ((g, pk), managed, live)) out n) :
    liveLength out.2 = live.length + n := by
  rw [taggedSign_denote] at h
  cases h with
  | queryBind _ _ c hc =>
      cases hc with
      | queryBind _ _ z hz => cases hz; simp [liveLength, liveWeight, OracleSpec.query, OracleQuery.mk, PFunctor.Obj.mk]

theorem taggedHash_liveLength (cost : PrimitiveCosts) (k : M × G₁) (g pk : G₁)
    (managed live : List ((M × G₁) × F)) (out) (n : Nat)
    (h : QueryCost liveWeight ((taggedHash.denote (arithmetic F G₁ G₂ K M cost)
      taggedSemantics (k, ())).run ((g, pk), managed, live)) out n) :
    liveLength out.2 = live.length + n := by
  rw [taggedHash_denote] at h
  cases hm : cacheMap managed k <;> cases hl : cacheMap live k <;>
    simp only [hm, hl, map_eq_bind_pure_comp, pure_bind, bind_assoc] at h
  all_goals cases h
  all_goals first | (rename_i tail; cases tail; simp [liveLength, liveWeight, OracleSpec.query, OracleQuery.mk, PFunctor.Obj.mk]) |
    simp [liveLength]

theorem taggedFinalHash_liveLength (cost : PrimitiveCosts) (k : M × G₁) (g pk : G₁)
    (managed live : List ((M × G₁) × F)) (out) (n : Nat)
    (h : QueryCost liveWeight ((taggedFinalHash.denote (arithmetic F G₁ G₂ K M cost)
      taggedSemantics (k, ())).run ((g, pk), managed, live)) out n) :
    liveLength out.2 = live.length + n := by
  rw [taggedFinalHash_denote] at h
  cases hl : cacheMap live k <;>
    simp only [hl, map_eq_bind_pure_comp, pure_bind, bind_assoc] at h
  all_goals cases h
  all_goals first | (rename_i tail; cases tail; simp [liveLength, liveWeight, OracleSpec.query, OracleQuery.mk, PFunctor.Obj.mk]) |
    simp [liveLength]

theorem taggedRoutines_liveLength (cost : PrimitiveCosts) (randomBound : Nat)
    {a b} (cmd : Command randomBound a b) (arg : a.Value (cryptoBase F G₁ G₂ K M))
    (state : cacheStore.Value (cryptoBase F G₁ G₂ K M)) (out) (n : Nat)
    (h : QueryCost liveWeight (((taggedRoutines randomBound cmd).denote
      (arithmetic F G₁ G₂ K M cost) taggedSemantics (arg, ())).run state) out n) :
    liveLength out.2 = liveLength state + n := by
  rcases state with ⟨⟨g, pk⟩, managed, live⟩
  cases cmd with
  | random arity =>
      simp only [taggedRoutines, Program.denote, taggedSemantics, StateT.run,
        map_eq_bind_pure_comp] at h
      cases h with
      | queryBind _ _ u hu => cases hu; simp [liveLength, liveWeight, OracleSpec.query, OracleQuery.mk, PFunctor.Obj.mk]
  | hash => exact taggedHash_liveLength cost arg g pk managed live out n h
  | sign => exact taggedSign_liveLength cost arg g pk managed live out n h

/-- Each fresh challenge appends exactly one chronological log entry; cache
hits and all private draws leave that count unchanged. -/
theorem macroPass_liveLength (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (state : cacheStore.Value (cryptoBase F G₁ G₂ K M)) (out) (n : Nat)
    (h : QueryCost liveWeight ((macroPass cost randomBound code env).run state) out n) :
    liveLength out.2 = liveLength state + n := by
  rw [macroPass, StateT.run_bind, Program.inline_denote] at h
  obtain ⟨first, k, m, hk, hm, rfl⟩ := (QueryCost.bind_iff _ _ _ _ _).1 h
  have hfirst := code.denote_queryPotential (arithmetic F G₁ G₂ K M cost)
    liveWeight liveLength _ (taggedRoutines_liveLength cost randomBound) env state first k hk
  simp only [bind_pure_comp, StateT.run_map] at hm
  obtain ⟨last, hlast, rfl⟩ := (QueryCost.map_iff _ _ _ _ _).1 hm
  have hlast := taggedFinalHash_liveLength cost _ first.2.1.1 first.2.1.2
    first.2.2.1 first.2.2.2 last m hlast
  dsimp only [liveLength] at hfirst hlast ⊢
  omega

theorem macroPass_trace_queryCost (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (g pk : G₁) (out) (n : Nat)
    (h : QueryCost liveWeight (cacheTrace <$>
      (macroPass cost randomBound code env).run ((g, pk), [], [])) out n) :
    out.queryLog.length = n := by
  obtain ⟨result, hr, rfl⟩ := (QueryCost.map_iff _ _ _ _ _).1 h
  have hc := macroPass_liveLength cost randomBound code env ((g, pk), [], []) result n hr
  simpa [cacheTrace, nativeTrace, nativeRepr, liveState, liveLength] using hc

/-- A selected slot is an actual live-hash occurrence on the typed path. -/
theorem macroPass_forkPoint_reachable (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (g pk : G₁) (qH : Nat) :
    PathCfReachable (cacheTrace <$> (macroPass cost randomBound code env).run ((g, pk), [], []))
      (fun _ => qH) (.inr ()) (FiatShamir.Fork.forkPoint G₁ F F M qH) := by
  apply pathCfReachable_of_queryCost
  intro out n hn slot hs
  have hlength := macroPass_trace_queryCost cost randomBound code env g pk out n hn
  have hslot := (List.getElem?_eq_some_iff.mp
    (FiatShamir.Fork.forkPoint_getElem?_eq_some_target
      (M := M) (Commit := G₁) (Resp := F) (Chal := F) hs)).1
  omega

end Signatures.Runtime.Schnorr
