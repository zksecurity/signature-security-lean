import Signatures.Runtime.CoronReduction
import Signatures.Runtime.CoronRefinement

/-! Exact correspondence of the complete costed evaluator to the named lazy co-CDH
reduction. This includes the automatically appended verification hash and final extraction. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Coron

variable {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]

noncomputable def nativeFinish (g X h : G₁) (qS : Nat) (out : M × G₁)
    (state : NativeState F M qS) : ProbComp G₁ :=
  (fun p => out.2 - (p.2.1.1 out.1).getD 0 • X) <$>
    (nativeReply g X h qS false out.1).run state

theorem finish_erase (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (qS : Nat) (out : M × G₁) (state : CacheState F M qS) :
    Run.value <$> finish (G₂ := G₂) cost sampling g X h qS out state =
      nativeFinish g X h qS out state.repr := by
  have hr := reply_refines (F := F) (G₂ := G₂) cost sampling g X h qS false out.1 state
  have hm := StateT.run_map (m := ProbComp) Run.value
    (reply (F := F) (G₂ := G₂) cost sampling g X h qS false out.1) state
  simp only [StateT.run] at hm hr
  rw [hm] at hr
  simp only [nativeFinish, StateT.run]
  rw [← hr]
  have hz : ((Expr.op CryptoOp.zero .unit : Expr CryptoOp [] scalar).run
      (arithmetic F G₁ G₂ M M cost) ()).value = 0 := rfl
  simp [finish, StateT.run, bind_pure_comp, CacheState.repr, hz, -Expr.run_value,
    extract_value (F := F) (G₂ := G₂) (M := M) cost,
    lookup_getD (arithmetic F G₁ G₂ M M cost) CryptoOp.messageEq (fun _ _ => rfl)]

noncomputable def nativeReduction (g X h : G₁) (qS : Nat)
    (oa : BLS.ROM.Adversary M G₁) : ProbComp G₁ := do
  let p ← (simulateQ (nativeOracle (F := F) g X h qS) oa).run
    ((fun _ => none, ∅), ∅)
  nativeFinish g X h qS p.1 p.2

theorem reduction_erase_native (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) {Γ}
    (code : Program CryptoOp (Command randomBound) Γ (.pair message point₁))
    (env : Env (cryptoBase F G₁ G₂ M M) Γ) :
    Run.value <$> reduction cost sampling g X h qS randomBound code env =
      nativeReduction (F := F) g X h qS
        (code.denote (arithmetic F G₁ G₂ M M cost) (sourceSemantics randomBound) env) := by
  have hs := simulation_refines cost sampling g X h qS randomBound code env .empty
  have hm := StateT.run_map (m := ProbComp) Run.value
    (code.run (arithmetic F G₁ G₂ M M cost) (handler cost sampling g X h qS randomBound) env) .empty
  simp only [StateT.run] at hs hm
  rw [hm] at hs
  have he : (CacheState.empty : CacheState F M qS).repr = ((fun _ => none, ∅), ∅) := rfl
  rw [he] at hs
  simp only [nativeReduction, StateT.run]
  rw [← hs]
  simp only [reduction, map_bind, bind_pure_comp, bind_map_left]
  congr 1
  funext p
  simpa using finish_erase (G₂ := G₂) cost sampling g X h qS p.1.value p.2

omit [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] in
theorem nativeReduction_cached (g X h : G₁) (qS : Nat)
    (oa : BLS.ROM.Adversary M G₁) :
    nativeReduction (F := F) g X h qS oa =
      (fun p => p.1.2 - (p.2.1.1 p.1.1).getD 0 • X) <$>
        (simulateQ (nativeOracle (F := F) g X h qS) (BLS.ROM.cacheForgery oa)).run
          ((fun _ => none, ∅), ∅) := by
  simp [nativeReduction, nativeFinish, BLS.ROM.cacheForgery, nativeOracle,
    map_bind, bind_pure_comp]

omit [AddCommGroup G₂] [Module F G₂] in
omit [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] in
/-- No distribution-only replacement is needed: the complete native solver is exactly
the existing named reduction, including `cacheForgeryPK`. -/
theorem nativeReduction_original (g X h : G₁) (g₂ X₂ : G₂) (qS : Nat)
    (adv : BLS.ROM.AdversaryPK M G₁ G₂) :
    nativeReduction (F := F) g X h qS (adv X₂) =
      BLS.CoCDH.coronReductionLazyPK (F := F) qS (BLS.ROM.cacheForgeryPK adv) g g₂ X X₂ h := by
  rw [nativeReduction_cached, nativeOracle_run]
  simp [BLS.CoCDH.coronReductionLazyPK, BLS.CoCDH.coronReductionProgram,
    BLS.ROM.cacheForgeryPK, StateT.run'_eq, bind_pure_comp]

/-- Complete evaluator erasure for an implementation of the adversary at the actual key.
The semantic premise identifies source code, not a finished solver or a runtime budget. -/
theorem reduction_erase (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (g₂ X₂ : G₂) (qS randomBound : Nat) {Γ}
    (code : Program CryptoOp (Command randomBound) Γ (.pair message point₁))
    (env : Env (cryptoBase F G₁ G₂ M M) Γ)
    (adv : BLS.ROM.AdversaryPK M G₁ G₂)
    (hsource : code.denote (arithmetic F G₁ G₂ M M cost) (sourceSemantics randomBound) env = adv X₂) :
    Run.value <$> reduction cost sampling g X h qS randomBound code env =
      BLS.CoCDH.coronReductionLazyPK (F := F) qS (BLS.ROM.cacheForgeryPK adv) g g₂ X X₂ h := by
  rw [reduction_erase_native, hsource]
  exact nativeReduction_original g X h g₂ X₂ qS adv

end Signatures.Runtime.Coron
