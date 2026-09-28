import Signatures.Runtime.CoronSimulation
import Signatures.BLS.CoCDH.Spec.Coron

/-! Behavioral correspondence of the concrete Coron caches and reply implementation to
the original lazy scalar/coin oracles. Representation functions are proof-only. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Coron

abbrev NativeState (F M : Type) (qS : Nat) :=
  ((M → Option F) × Finset M) × (M →ₒ Fin (qS + 1)).QueryCache

def CacheState.repr {F M qS} [DecidableEq M] (state : CacheState F M qS) : NativeState F M qS :=
  ((cacheMap state.scalars, state.signed.toFinset), listQueryCache state.coins)

variable {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]

noncomputable def nativeReply (g X h : G₁) (qS : Nat) (signing : Bool) (m : M) :
    StateT (NativeState F M qS) ProbComp G₁ := fun state => do
  let signed := if signing then insert m state.1.2 else state.1.2
  let rho ← (BLS.CoCDH.Tight.getDlogS (F := F) m).run (state.1.1, signed)
  let k ← ((M →ₒ Fin (qS + 1)).randomOracle m).run state.2
  pure ((if signing then (if k.1 = 0 then 0 else rho.1 • X)
    else rho.1 • g + if k.1 = 0 then h else 0), (rho.2, k.2))

omit [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] in
theorem nativeReply_run (g X h : G₁) (qS : Nat) (signing : Bool) (m : M)
    (state : NativeState F M qS) :
    (nativeReply g X h qS signing m).run state = (do
      let rho ← (BLS.CoCDH.Tight.getDlogS (F := F) m).run
        (state.1.1, if signing then insert m state.1.2 else state.1.2)
      let k ← ((M →ₒ Fin (qS + 1)).randomOracle m).run state.2
      pure ((if signing then (if k.1 = 0 then 0 else rho.1 • X)
        else rho.1 • g + if k.1 = 0 then h else 0), (rho.2, k.2))) := rfl

theorem reply_refines (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (qS : Nat) (signing : Bool) (m : M) :
    StateRefines CacheState.repr (Run.value <$> reply (F := F) (G₂ := G₂) cost sampling g X h qS signing m)
      (nativeReply (F := F) g X h qS signing m) := by
  intro state
  have hr := cacheHandler_getDlogS (arithmetic F G₁ G₂ M M cost) (draws qS sampling)
    CryptoOp.messageEq Draw.scalar (fun _ _ => rfl) (by simp [draws]) m 0 state.scalars
      (if signing then insert m state.signed.toFinset else state.signed.toFinset)
  have hc := cacheHandler_randomOracle (arithmetic F G₁ G₂ M M cost) (draws qS sampling)
    CryptoOp.messageEq Draw.coin (fun _ _ => rfl) (by simp [draws]; rfl) m 0 state.coins
  have hm := StateT.run_map (m := ProbComp) Run.value
    (reply (F := F) (G₂ := G₂) cost sampling g X h qS signing m) state
  simp only [StateT.run] at hm
  simp only [StateT.run] at hr hc
  simp only [nativeReply, StateT.run, CacheState.repr]
  rw [← hr, ← hc, hm]
  have hz : ((Expr.op CryptoOp.zero .unit : Expr CryptoOp [] scalar).run
      (arithmetic F G₁ G₂ M M cost) ()).value = 0 := rfl
  cases signing <;>
    simp [reply, StateT.run, map_bind, bind_map_left, hz, -Expr.run_value,
      coinValue_run (F := F) (G₁ := G₁) (G₂ := G₂) (M := M) cost qS,
      hashReply_value (F := F) (G₂ := G₂) (M := M) cost,
      signReply_value (F := F) (G₂ := G₂) (M := M) cost]

noncomputable def nativeOracle (g X h : G₁) (qS : Nat) :
    QueryImpl (BLS.CoCDH.Tight.advSpec M G₁) (StateT (NativeState F M qS) ProbComp) :=
  fun q => match q with
  | .inl (.inl n) => fun state =>
      (fun x => (x, state)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
  | .inl (.inr m) => nativeReply g X h qS false m
  | .inr m => nativeReply g X h qS true m

omit [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] in
/-- Flattening the two original state transformers gives the same per-query behavior.
The original signing set and both lazy caches are retained in this correspondence. -/
theorem nativeOracle_original (g X h : G₁) (qS : Nat)
    (q : (BLS.CoCDH.Tight.advSpec M G₁).Domain) (state : NativeState F M qS) :
    (nativeOracle g X h qS q).run state =
      (fun p => (p.1.1, (p.1.2, p.2))) <$>
        (simulateQ (BLS.CoCDH.lazyCoinImpl (D := M) (R := Fin (qS + 1)))
          ((BLS.CoCDH.coronOracleLazy (F := F) g X h qS q).run state.1)).run state.2 := by
  rcases q with (n | m) | m
  · simp [nativeOracle, BLS.CoCDH.coronOracleLazy, BLS.CoCDH.lazyCoinImpl, unifFwdImpl]
    rfl
  · simp only [nativeOracle, nativeReply_run]
    simp [BLS.CoCDH.coronOracleLazy, BLS.CoCDH.lazyCoinImpl,
      roSim.run_liftM, map_bind, bind_map_left]
  · simp only [nativeOracle, nativeReply_run]
    simp [BLS.CoCDH.coronOracleLazy, BLS.CoCDH.lazyCoinImpl,
      roSim.run_liftM, map_bind, bind_map_left]

noncomputable def sourceSemantics (randomBound : Nat) :
    Semantics (cryptoBase F G₁ G₂ M M) (Command randomBound) (BLS.CoCDH.Tight.advSpec M G₁) :=
  fun cmd arg => match cmd with
  | .random n => liftM ((BLS.CoCDH.Tight.advSpec M G₁).query (.inl (.inl n.val)))
  | .hash => liftM ((BLS.CoCDH.Tight.advSpec M G₁).query (.inl (.inr arg)))
  | .sign => liftM ((BLS.CoCDH.Tight.advSpec M G₁).query (.inr arg))

theorem handler_refines (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) {a b} (cmd : Command randomBound a b)
    (arg : a.Value (cryptoBase F G₁ G₂ M M)) :
    StateRefines CacheState.repr
      (Run.value <$> handler cost sampling g X h qS randomBound cmd arg)
      (simulateQ (nativeOracle (F := F) g X h qS) (sourceSemantics randomBound cmd arg)) := by
  cases cmd with
  | random n =>
      intro state
      have hm := StateT.run_map (m := ProbComp) Run.value
        (handler (F := F) (G₂ := G₂) cost sampling g X h qS randomBound (.random n) arg) state
      simp only [StateT.run] at hm ⊢
      rw [hm]
      simp [handler, sourceSemantics, nativeOracle]
  | hash => simpa [handler, sourceSemantics, nativeOracle] using
      reply_refines (F := F) (G₂ := G₂) cost sampling g X h qS false arg
  | sign => simpa [handler, sourceSemantics, nativeOracle] using
      reply_refines (F := F) (G₂ := G₂) cost sampling g X h qS true arg

/-- The runtime simulation and the native lazy simulation agree for every first-order
adaptive source program. No nonadaptive query schedule is assumed. -/
theorem simulation_refines (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) {Γ a}
    (code : Program CryptoOp (Command randomBound) Γ a)
    (env : Env (cryptoBase F G₁ G₂ M M) Γ) :
    StateRefines CacheState.repr
      (Run.value <$> code.run (arithmetic F G₁ G₂ M M cost)
        (handler cost sampling g X h qS randomBound) env)
      (simulateQ (nativeOracle g X h qS)
        (code.denote (arithmetic F G₁ G₂ M M cost) (sourceSemantics randomBound) env)) := by
  rw [Program.run_erase, Program.denote_simulate]
  exact code.denote_refines (arithmetic F G₁ G₂ M M cost) CacheState.repr _ _
    (handler_refines cost sampling g X h qS randomBound) env

omit [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] in
/-- Per-query correspondence extends to arbitrary adaptive `OracleComp` continuations. -/
theorem nativeOracle_run (g X h : G₁) (qS : Nat) {α : Type}
    (oa : OracleComp (BLS.CoCDH.Tight.advSpec M G₁) α) (state : NativeState F M qS) :
    (simulateQ (nativeOracle g X h qS) oa).run state =
      (fun p => (p.1.1, (p.1.2, p.2))) <$>
        (simulateQ (BLS.CoCDH.lazyCoinImpl (D := M) (R := Fin (qS + 1)))
          ((simulateQ (BLS.CoCDH.coronOracleLazy (F := F) g X h qS) oa).run state.1)).run state.2 := by
  induction oa using OracleComp.inductionOn generalizing state with
  | pure x => simp
  | query_bind q k ih =>
      simp only [simulateQ_bind, simulateQ_query, StateT.run_bind]
      simp only [OracleSpec.query, OracleQuery.cont_mk, OracleQuery.input_mk, id_map]
      rw [nativeOracle_original]
      simp only [bind_map_left, map_bind]
      congr 1
      funext p
      simpa [map_bind, bind_map_left] using ih p.1.1 (p.1.2, p.2)

end Signatures.Runtime.Coron
