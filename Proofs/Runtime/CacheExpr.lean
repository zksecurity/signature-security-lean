import Proofs.Runtime.LookupExpr
import Proofs.Runtime.Program

/-! Association-list cache procedures with compiled structured-key comparison.
All scans and updates are first-order syntax; only the supplied draw command is effectful. -/

open OracleComp OracleSpec

namespace Signatures.Runtime

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}
  {key val : Ty Atom}

def cacheGetExpr (eq : Expr Op [key, key] .bool) (draw : Cmd .unit val) :
    Program Op Cmd [key, val, .list (.pair key val)] (.pair val (.list (.pair key val))) :=
  .bind (.ret (lookupExpr eq))
    (.branch (.fst (.var .here))
      (.ret (.pair (.snd (.var .here)) (.var (.there (.there (.there .here))))))
      (.bind (.query draw .unit)
        (.ret (.pair (.var .here)
          (.cons (.pair (.var (.there (.there .here))) (.var .here))
            (.var (.there (.there (.there (.there .here))))))))))

/-- Programming never overwrites a cached answer, including a cached zero. -/
def cacheProgram (eq : Expr Op [key, key] .bool) :
    Expr Op [key, val, .list (.pair key val)] (.list (.pair key val)) :=
  .letE (lookupExpr eq)
    (.branch (.fst (.var .here)) (.var (.there (.there (.there .here))))
      (.cons (.pair (.var (.there .here)) (.var (.there (.there .here))))
        (.var (.there (.there (.there .here))))))

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem cacheGetExpr_run (P : Primitives base Op) (H : HandlerM base Cmd m)
    (eq : Expr Op [key, key] .bool) (draw : Cmd .unit val)
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base)) :
    (cacheGetExpr eq draw).run P H (k, default, xs, ()) =
      let found := (lookupExpr eq).run P (k, default, xs, ())
      if found.value.1 = true then pure ⟨(found.value.2, xs), found.steps + 13⟩
      else (fun r => ⟨(r.value, (k, r.value) :: xs), found.steps + r.steps + 22⟩) <$> H draw () := by
  unfold cacheGetExpr
  generalize lookupExpr eq = lookup
  by_cases h : (lookup.run P (k, default, xs, ())).value.1 = true
  · simp [Program.run, Expr.run, Var.get, Var.depth, h, -Expr.run_value]
  · simp [Program.run, Expr.run, Var.get, Var.depth, h, -Expr.run_value, bind_pure_comp]
    congr 1
    funext r
    congr 1
    omega

theorem cacheGetExpr_denote (P : Primitives base Op) (H : SemanticsM base Cmd m)
    (eq : Expr Op [key, key] .bool) (draw : Cmd .unit val)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, eq.denote P (x, y, ()) = decide (x = y))
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base)) :
    (cacheGetExpr eq draw).denote P H (k, default, xs, ()) =
      if (lookupValue k default xs).1 = true then pure ((lookupValue k default xs).2, xs)
      else (fun v => (v, (k, v) :: xs)) <$> H draw () := by
  have hl : (lookupExpr eq).denote P (k, default, xs, ()) = lookupValue k default xs := by
    rw [← Expr.run_value]
    exact lookupExpr_value P eq heq k default xs
  by_cases h : (lookupValue k default xs).1 = true <;>
    simp [cacheGetExpr, Program.denote, Expr.denote, Var.get, hl, h, bind_pure_comp]

omit [Monad m] [LawfulMonad m] in
theorem cacheProgram_value (P : Primitives base Op) (eq : Expr Op [key, key] .bool)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, eq.denote P (x, y, ()) = decide (x = y))
    (k : key.Value base) (v : val.Value base) (xs : List (key.Value base × val.Value base)) :
    ((cacheProgram eq).run P (k, v, xs, ())).value =
      if (lookupValue k v xs).1 = true then xs else (k, v) :: xs := by
  simp only [cacheProgram, Expr.run, Var.get]
  rw [lookupExpr_value P eq heq]
  split <;> rename_i h <;> simp [h]

omit [Monad m] [LawfulMonad m] in
theorem cacheProgram_length (P : Primitives base Op) (eq : Expr Op [key, key] .bool)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, eq.denote P (x, y, ()) = decide (x = y))
    (k : key.Value base) (v : val.Value base) (xs : List (key.Value base × val.Value base)) :
    ((cacheProgram eq).run P (k, v, xs, ())).value.length ≤ xs.length + 1 := by
  rw [cacheProgram_value P eq heq]
  split <;> simp

omit [Monad m] [LawfulMonad m] in
theorem cacheProgram_steps_le (P : Primitives base Op) (eq : Expr Op [key, key] .bool)
    (cEq : Nat) (heq : ∀ x y, (eq.run P (x, y, ())).steps ≤ cEq)
    (k : key.Value base) (v : val.Value base) (xs : List (key.Value base × val.Value base)) :
    ((cacheProgram eq).run P (k, v, xs, ())).steps ≤ xs.length * (cEq + 22) + 24 := by
  have hl := lookupExpr_steps_le P eq cEq heq k v xs
  by_cases h : ((lookupExpr eq).run P (k, v, xs, ())).value.1 = true <;>
    simp only [cacheProgram, Expr.run, Var.get, Var.depth, h, ite_true,
      Bool.false_eq_true, ite_false] <;> omega

variable {I S : Type} {spec : OracleSpec I}

omit [Monad m] [LawfulMonad m] in
/-- The draw may change an ambient store, such as the replay tape. Cache code preserves
that returned store and adds no unaccounted effect. -/
theorem cacheGetExpr_bound (P : Primitives base Op)
    (H : HandlerM base Cmd (StateT S (OracleComp spec)))
    (eq : Expr Op [key, key] .bool) (draw : Cmd .unit val) (cEq cDraw : Nat)
    (heq : ∀ x y, (eq.run P (x, y, ())).steps ≤ cEq)
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base))
    (s : S) (hdraw : ∀ r ∈ support ((H draw ()).run s), r.1.steps ≤ cDraw)
    (z : Run (val.Value base × List (key.Value base × val.Value base)) × S)
    (hz : z ∈ support (((cacheGetExpr eq draw).run P H (k, default, xs, ())).run s)) :
    z.1.steps ≤ xs.length * (cEq + 22) + cDraw + 31 ∧
      z.1.value.2.length ≤ xs.length + 1 := by
  have hl := lookupExpr_steps_le P eq cEq heq k default xs
  rw [cacheGetExpr_run] at hz
  dsimp only at hz
  split at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨by dsimp; omega, Nat.le_succ _⟩
  · simp only [StateT.run_map, support_map, Set.mem_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    have hd := hdraw r hr
    exact ⟨by dsimp; omega, le_rfl⟩

omit [Monad m] [LawfulMonad m] in
theorem cacheGetExpr_state (P : Primitives base Op)
    (H : HandlerM base Cmd (StateT S (OracleComp spec)))
    (eq : Expr Op [key, key] .bool) (draw : Cmd .unit val)
    (inv : S → Prop) (size : S → Nat)
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base))
    (s : S) (hs : inv s)
    (hdraw : ∀ r ∈ support ((H draw ()).run s), inv r.2 ∧ size r.2 ≤ size s + 1)
    (z : Run (val.Value base × List (key.Value base × val.Value base)) × S)
    (hz : z ∈ support (((cacheGetExpr eq draw).run P H (k, default, xs, ())).run s)) :
    inv z.2 ∧ size z.2 ≤ size s + 1 := by
  rw [cacheGetExpr_run] at hz
  dsimp only at hz
  split at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hs, Nat.le_succ _⟩
  · simp only [StateT.run_map, support_map, Set.mem_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    exact hdraw r hr

end Signatures.Runtime
