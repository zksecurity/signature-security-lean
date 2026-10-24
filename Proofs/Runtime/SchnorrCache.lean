import Proofs.Runtime.CacheExpr
import Proofs.Runtime.Schnorr

/-! Executable Schnorr cache operations. The signing simulator's programmed cache and
the live random-oracle cache are distinct, explicitly passed association lists. -/

open OracleComp

namespace Signatures.Runtime.Schnorr

abbrev hashKey : Ty CryptoAtom := .pair message point₁
abbrev hashCache : Ty CryptoAtom := .list (.pair hashKey scalar)

def hashEq : Expr CryptoOp [hashKey, hashKey] .bool :=
  .branch (.op .messageEq (.pair (.fst (.var .here)) (.fst (.var (.there .here)))))
    (.op .point₁Eq (.pair (.snd (.var .here)) (.snd (.var (.there .here)))))
    (.bool false)

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
private def v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))
private def v4 {a b c d e Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: Γ) e :=
  .var (.there (.there (.there (.there .here))))

variable {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}

/-- A managed hit skips the live oracle. A managed miss consults the independent
live cache and then stores that answer in the managed cache. -/
def managedGet (draw : Cmd .unit scalar) :
    Program CryptoOp Cmd [hashKey, scalar, hashCache, hashCache]
      (.pair scalar (.pair hashCache hashCache)) :=
  .bind (.call (.ret (lookupExpr hashEq))
    (.cons v0 (.cons v1 (.cons v2 .nil))))
    (.branch (.fst v0)
      (.ret (.pair (.snd v0) (.pair v3 v4)))
      (.bind (.call (cacheGetExpr hashEq draw)
        (.cons v1 (.cons v2 (.cons v4 .nil))))
        (.ret (.pair (.fst v0)
          (.pair (.cons (.pair v2 (.fst v0)) v4) (.snd v0))))))

/-- A simulated signature programs only the managed cache. An existing challenge is
preserved even if it differs from the simulator's challenge; the proof pays for collisions. -/
def signCached (draw : Cmd .unit scalar) :
    Program CryptoOp Cmd [message, point₁, point₁, hashCache]
      (.pair (.pair point₁ scalar) hashCache) :=
  .bind (.query draw .unit)
    (.bind (.query draw .unit)
      (.bind (.call (.ret simulatedCommit)
        (.cons v0 (.cons v1 (.cons v3 (.cons v4 .nil)))))
        (.bind (.call (.ret (cacheProgram hashEq))
          (.cons (.pair v3 v0) (.cons v2 (.cons (.var (.there (.there (.there (.there (.there (.there .here))))))) .nil))))
          (.ret (.pair (.pair v1 v2) v0)))))

variable {F G₁ G₂ K M : Type} [Field F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem hashEq_value (cost : PrimitiveCosts) (x y : M × G₁) :
    hashEq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y) := by
  by_cases h : x.1 = y.1 <;>
    simp [hashEq, Expr.denote, Var.get, arithmetic, h, Prod.ext_iff]
  exact decide_eq_decide.mpr Iff.rfl

theorem hashEq_steps_le (cost : PrimitiveCosts) (x y : M × G₁) :
    (hashEq.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤
      cost.messageEq + cost.point₁Eq + 15 := by
  by_cases h : x.1 = y.1 <;>
    simp [hashEq, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price, h] <;> omega

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem managedGet_denote (cost : PrimitiveCosts)
    (H : SemanticsM (cryptoBase F G₁ G₂ K M) Cmd m) (draw : Cmd .unit scalar)
    (k : M × G₁) (default : F) (managed live : List ((M × G₁) × F)) :
    (managedGet draw).denote (arithmetic F G₁ G₂ K M cost) H (k, default, managed, live, ()) =
      if (lookupValue k default managed).1 = true then
        pure ((lookupValue k default managed).2, managed, live)
      else (fun p => (p.1, (k, p.1) :: managed, p.2)) <$>
        (cacheGetExpr hashEq draw).denote (arithmetic F G₁ G₂ K M cost) H
          (k, default, live, ()) := by
  have hl : (lookupExpr (val := scalar) hashEq).denote (arithmetic F G₁ G₂ K M cost)
      (k, default, managed, ()) = lookupValue k default managed := by
    rw [← Expr.run_value]
    exact lookupExpr_value (val := scalar) (arithmetic F G₁ G₂ K M cost) hashEq
      (hashEq_value (F := F) (G₂ := G₂) (K := K) cost) k default managed
  by_cases h : (lookupValue k default managed).1 = true <;>
    simp [managedGet, Program.denote, Args.denote, Expr.denote,
      v0, v1, v2, v3, v4, Var.get, hl, h, bind_pure_comp]

theorem managedGet_run (cost : PrimitiveCosts)
    (H : HandlerM (cryptoBase F G₁ G₂ K M) Cmd m) (draw : Cmd .unit scalar)
    (k : M × G₁) (default : F) (managed live : List ((M × G₁) × F)) :
    (managedGet draw).run (arithmetic F G₁ G₂ K M cost) H (k, default, managed, live, ()) =
      let found := (lookupExpr (val := scalar) hashEq).run (arithmetic F G₁ G₂ K M cost) (k, default, managed, ())
      if found.value.1 = true then pure ⟨(found.value.2, managed, live), found.steps + 31⟩
      else (fun r => ⟨(r.value.1, (k, r.value.1) :: managed, r.value.2),
        found.steps + r.steps + 53⟩) <$>
        (cacheGetExpr hashEq draw).run (arithmetic F G₁ G₂ K M cost) H (k, default, live, ()) := by
  unfold managedGet
  generalize lookupExpr hashEq = lookup
  by_cases h : (lookup.run (arithmetic F G₁ G₂ K M cost) (k, default, managed, ())).value.1 = true
  · simp [Program.run, Args.run, Expr.run, v0, v1, v2, v3, v4,
      Var.get, Var.depth, h, -Expr.run_value]
    congr 2
    omega
  · simp [Program.run, Args.run, Expr.run, v0, v1, v2, v3, v4,
      Var.get, Var.depth, h, -Expr.run_value, bind_pure_comp, Functor.map_map]
    congr 1
    funext r
    congr 1
    omega

theorem signCached_run (cost : PrimitiveCosts)
    (H : HandlerM (cryptoBase F G₁ G₂ K M) Cmd m) (draw : Cmd .unit scalar)
    (msg : M) (g pk : G₁) (managed : List ((M × G₁) × F)) :
    (signCached draw).run (arithmetic F G₁ G₂ K M cost) H (msg, g, pk, managed, ()) = (do
      let c ← H draw ()
      let z ← H draw ()
      let R := simulatedCommit.run (arithmetic F G₁ G₂ K M cost) (z.value, c.value, g, pk, ())
      let programmed := (cacheProgram hashEq).run (arithmetic F G₁ G₂ K M cost)
        ((msg, R.value), c.value, managed, ())
      pure ⟨((R.value, z.value), programmed.value),
        c.steps + z.steps + R.steps + programmed.steps + 60⟩) := by
  unfold signCached
  generalize simulatedCommit = commit
  generalize cacheProgram hashEq = program
  simp [Program.run, Args.run, Expr.run, v0, v1, v2, v3, v4,
    Var.get, Var.depth, -Expr.run_value]
  congr 1
  funext c
  congr 1
  funext z
  congr 1
  omega

theorem signCached_denote (cost : PrimitiveCosts)
    (H : SemanticsM (cryptoBase F G₁ G₂ K M) Cmd m) (draw : Cmd .unit scalar)
    (msg : M) (g pk : G₁) (managed : List ((M × G₁) × F)) :
    (signCached draw).denote (arithmetic F G₁ G₂ K M cost) H (msg, g, pk, managed, ()) = (do
      let c ← H draw ()
      let z ← H draw ()
      let R := z • g - c • pk
      pure ((R, z), ((cacheProgram hashEq).run (arithmetic F G₁ G₂ K M cost)
        ((msg, R), c, managed, ())).value)) := by
  simp [signCached, Program.denote, Args.denote, Expr.denote, v0, v1, v2, v3, v4,
    Var.get, simulatedCommit, arithmetic]

variable {I S : Type} {spec : OracleSpec I}

omit [Monad m] [LawfulMonad m] in
theorem managedGet_bound (cost : PrimitiveCosts)
    (H : HandlerM (cryptoBase F G₁ G₂ K M) Cmd (StateT S (OracleComp spec)))
    (draw : Cmd .unit scalar) (cDraw : Nat)
    (k : M × G₁) (default : F) (managed live : List ((M × G₁) × F)) (s : S)
    (hdraw : ∀ r ∈ support ((H draw ()).run s), r.1.steps ≤ cDraw)
    (out : Run (F × List ((M × G₁) × F) × List ((M × G₁) × F)) × S)
    (hout : out ∈ support (((managedGet draw).run (arithmetic F G₁ G₂ K M cost) H
      (k, default, managed, live, ())).run s)) :
    out.1.steps ≤ (managed.length + live.length) * (cost.messageEq + cost.point₁Eq + 37) + cDraw + 93 ∧
      out.1.value.2.1.length ≤ managed.length + 1 ∧
      out.1.value.2.2.length ≤ live.length + 1 := by
  have hl := lookupExpr_steps_le (val := scalar) (arithmetic F G₁ G₂ K M cost) hashEq
    (cost.messageEq + cost.point₁Eq + 15)
    (hashEq_steps_le (F := F) (G₂ := G₂) (K := K) cost) k default managed
  rw [managedGet_run] at hout
  dsimp only at hout
  split at hout
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
    subst out
    refine ⟨?_, Nat.le_succ _, Nat.le_succ _⟩
    dsimp
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_mul] at *
    omega
  · simp only [StateT.run_map, support_map, Set.mem_image] at hout
    obtain ⟨r, hr, rfl⟩ := hout
    have hc := cacheGetExpr_bound (arithmetic F G₁ G₂ K M cost) H hashEq draw
      (cost.messageEq + cost.point₁Eq + 15) cDraw
      (hashEq_steps_le (F := F) (G₂ := G₂) (K := K) cost) k default live s hdraw r hr
    refine ⟨?_, le_rfl, hc.2⟩
    dsimp
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_mul] at *
    omega

omit [Monad m] [LawfulMonad m] in
theorem signCached_bound_of_invariant (cost : PrimitiveCosts)
    (H : HandlerM (cryptoBase F G₁ G₂ K M) Cmd (StateT S (OracleComp spec)))
    (draw : Cmd .unit scalar) (cDraw : Nat)
    (inv : S → Prop) (size : S → Nat)
    (hdraw : ∀ s, inv s → ∀ r ∈ support ((H draw ()).run s),
      inv r.2 ∧ size r.2 ≤ size s + 1 ∧ r.1.steps ≤ cDraw)
    (msg : M) (g pk : G₁) (managed : List ((M × G₁) × F)) (s : S)
    (hs : inv s) (out : Run ((G₁ × F) × List ((M × G₁) × F)) × S)
    (hout : out ∈ support (((signCached draw).run (arithmetic F G₁ G₂ K M cost) H
      (msg, g, pk, managed, ())).run s)) :
    out.1.steps ≤ managed.length * (cost.messageEq + cost.point₁Eq + 37) +
      2 * cDraw + 2 * cost.scalar₁ + cost.group + 100 ∧
      out.1.value.2.length ≤ managed.length + 1 ∧ inv out.2 ∧ size out.2 ≤ size s + 2 := by
  rw [signCached_run] at hout
  simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hout
  obtain ⟨c, hc, z, hz, rfl⟩ := hout
  have hc' := hdraw s hs c hc
  have hz' := hdraw c.2 hc'.1 z hz
  let R := simulatedCommit.run (arithmetic F G₁ G₂ K M cost) (z.1.value, c.1.value, g, pk, ())
  have hR : R.steps = 2 * cost.scalar₁ + cost.group + 16 := by
    dsimp [R, simulatedCommit, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price]
    omega
  have hp := cacheProgram_steps_le (val := scalar) (arithmetic F G₁ G₂ K M cost) hashEq
    (cost.messageEq + cost.point₁Eq + 15)
    (hashEq_steps_le (F := F) (G₂ := G₂) (K := K) cost) (msg, R.value) c.1.value managed
  have hn := cacheProgram_length (val := scalar) (arithmetic F G₁ G₂ K M cost) hashEq
    (hashEq_value (F := F) (G₂ := G₂) (K := K) cost) (msg, R.value) c.1.value managed
  refine ⟨?_, hn, hz'.1, by dsimp; omega⟩
  dsimp only
  dsimp only [R] at hR hp
  simp only [Nat.add_assoc, Nat.reduceAdd] at *
  omega

omit [Monad m] [LawfulMonad m] in
theorem signCached_bound (cost : PrimitiveCosts)
    (H : HandlerM (cryptoBase F G₁ G₂ K M) Cmd (StateT S (OracleComp spec)))
    (draw : Cmd .unit scalar) (cDraw : Nat)
    (hdraw : ∀ s r, r ∈ support ((H draw ()).run s) → r.1.steps ≤ cDraw)
    (msg : M) (g pk : G₁) (managed : List ((M × G₁) × F)) (s : S)
    (out : Run ((G₁ × F) × List ((M × G₁) × F)) × S)
    (hout : out ∈ support (((signCached draw).run (arithmetic F G₁ G₂ K M cost) H
      (msg, g, pk, managed, ())).run s)) :
    out.1.steps ≤ managed.length * (cost.messageEq + cost.point₁Eq + 37) +
      2 * cDraw + 2 * cost.scalar₁ + cost.group + 100 ∧
      out.1.value.2.length ≤ managed.length + 1 := by
  have h := signCached_bound_of_invariant cost H draw cDraw (fun _ => True) (fun _ => 0)
    (fun s _ r hr => ⟨trivial, by simp, hdraw s r hr⟩) msg g pk managed s trivial out hout
  exact ⟨h.1, h.2.1⟩

omit [Monad m] [LawfulMonad m] in
theorem managedGet_state (cost : PrimitiveCosts)
    (H : HandlerM (cryptoBase F G₁ G₂ K M) Cmd (StateT S (OracleComp spec)))
    (draw : Cmd .unit scalar) (inv : S → Prop) (size : S → Nat)
    (k : M × G₁) (default : F) (managed live : List ((M × G₁) × F))
    (s : S) (hs : inv s)
    (hdraw : ∀ r ∈ support ((H draw ()).run s), inv r.2 ∧ size r.2 ≤ size s + 1)
    (z : Run (F × List ((M × G₁) × F) × List ((M × G₁) × F)) × S)
    (hz : z ∈ support (((managedGet draw).run (arithmetic F G₁ G₂ K M cost) H
      (k, default, managed, live, ())).run s)) : inv z.2 ∧ size z.2 ≤ size s + 1 := by
  rw [managedGet_run] at hz
  dsimp only at hz
  split at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hs, Nat.le_succ _⟩
  · simp only [StateT.run_map, support_map, Set.mem_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    exact cacheGetExpr_state (arithmetic F G₁ G₂ K M cost) H hashEq draw inv size
      k default live s hs hdraw r hr

end Signatures.Runtime.Schnorr
