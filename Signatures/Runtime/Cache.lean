import Signatures.Runtime.Lookup
import Signatures.Runtime.Program

/-! Persistent cache access as first-order runtime code. Hits return the stored value without
sampling; misses draw once and prepend a key/value cell. The table is an association list,
so no constant-time dictionary or hidden pure lookup is assumed. -/

open OracleComp OracleSpec

namespace Signatures.Runtime

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}
  {key val : Ty Atom} {I : Type} {spec : OracleSpec I}

def cacheGet (eq : Op (.pair key key) .bool) (draw : Cmd .unit val) :
    Program Op Cmd [key, val, .list (.pair key val)] (.pair val (.list (.pair key val))) :=
  .bind (.ret (lookup eq))
    (.branch (.fst (.var .here))
      (.ret (.pair (.snd (.var .here)) (.var (.there (.there (.there .here))))))
      (.bind (.query draw .unit)
        (.ret (.pair (.var .here)
          (.cons (.pair (.var (.there (.there .here))) (.var .here))
            (.var (.there (.there (.there (.there .here))))))))))

theorem cacheGet_denote (P : Primitives base Op) (H : Semantics base Cmd spec)
    (eq : Op (.pair key key) .bool) (draw : Cmd .unit val)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base)) :
    (cacheGet eq draw).denote P H (k, default, xs, ()) =
      if (lookupValue k default xs).1 = true then pure ((lookupValue k default xs).2, xs)
      else (fun v => (v, (k, v) :: xs)) <$> H draw () := by
  have hv : (lookup eq).denote P (k, default, xs, ()) = lookupValue k default xs := by
    rw [← Expr.run_value]
    exact lookup_correct P eq heq k default xs
  by_cases hb : (lookupValue k default xs).1 = true <;>
    simp [cacheGet, Program.denote, hv, Expr.denote, Var.get, hb, bind_pure_comp]

theorem cacheGet_steps_le (P : Primitives base Op) (H : Handler base Cmd spec)
    (eq : Op (.pair key key) .bool) (draw : Cmd .unit val) (cEq cDraw : Nat)
    (heq : ∀ x y, P.cost eq (x, y) ≤ cEq)
    (hdraw : ∀ r ∈ support (H draw ()), r.steps ≤ cDraw)
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base))
    (z : Run (val.Value base × List (key.Value base × val.Value base)))
    (hz : z ∈ support ((cacheGet eq draw).run P H (k, default, xs, ()))) :
    z.steps ≤ xs.length * (cEq + 19) + cDraw + 31 := by
  have hl := lookup_steps_le P eq cEq heq k default xs
  by_cases h : ((lookup eq).run P (k, default, xs, ())).value.1 = true
  · simp only [cacheGet, Program.run, Expr.run, Var.get, Var.depth, pure_bind, h,
      ite_true, support_pure, Set.mem_singleton_iff] at hz
    subst z
    dsimp
    omega
  · simp only [cacheGet, Program.run, Expr.run, Var.get, Var.depth, pure_bind, h,
      Bool.false_eq_true, ite_false, bind_assoc, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    have hd := hdraw r hr
    dsimp
    omega

/-- Packing three input slots and unpacking the two returned components costs five steps.
The fixed default value is an input to this procedure; its initialization is not hidden here. -/
def cacheHandler (P : Primitives base Op) (H : Handler base Cmd spec)
    (eq : Op (.pair key key) .bool) (draw : Cmd .unit val) (default : val.Value base)
    (k : key.Value base) : StateT (List (key.Value base × val.Value base)) (OracleComp spec)
      (Run (val.Value base)) := fun xs => do
  let r ← (cacheGet eq draw).run P H (k, default, xs, ())
  pure (⟨r.value.1, r.steps + 5⟩, r.value.2)

theorem cacheHandler_steps_le (P : Primitives base Op) (H : Handler base Cmd spec)
    (eq : Op (.pair key key) .bool) (draw : Cmd .unit val) (cEq cDraw : Nat)
    (heq : ∀ x y, P.cost eq (x, y) ≤ cEq)
    (hdraw : ∀ r ∈ support (H draw ()), r.steps ≤ cDraw)
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base))
    (z : Run (val.Value base) × List (key.Value base × val.Value base))
    (hz : z ∈ support ((cacheHandler P H eq draw default k).run xs)) :
    z.1.steps ≤ xs.length * (cEq + 19) + cDraw + 36 := by
  simp only [cacheHandler, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  have h := cacheGet_steps_le P H eq draw cEq cDraw heq hdraw k default xs r hr
  dsimp
  omega

theorem cacheHandler_erase (P : Primitives base Op) (H : Handler base Cmd spec)
    (eq : Op (.pair key key) .bool) (draw : Cmd .unit val)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base)) :
    (fun z => (z.1.value, z.2)) <$> (cacheHandler P H eq draw default k).run xs =
      if (lookupValue k default xs).1 = true then pure ((lookupValue k default xs).2, xs)
      else (fun r => (r.value, (k, r.value) :: xs)) <$> H draw () := by
  have h := cacheGet_denote P (fun cmd x => Run.value <$> H cmd x) eq draw heq k default xs
  rw [← Program.run_erase] at h
  simpa [cacheHandler, StateT.run, map_bind, bind_pure_comp] using h

theorem cacheHandler_length (P : Primitives base Op) (H : Handler base Cmd spec)
    (eq : Op (.pair key key) .bool) (draw : Cmd .unit val)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base))
    (z : Run (val.Value base) × List (key.Value base × val.Value base))
    (hz : z ∈ support ((cacheHandler P H eq draw default k).run xs)) :
    z.2.length ≤ xs.length + 1 := by
  have hv : (z.1.value, z.2) ∈ support
      ((fun z => (z.1.value, z.2)) <$> (cacheHandler P H eq draw default k).run xs) := by
    rw [support_map]
    exact ⟨z, hz, rfl⟩
  rw [cacheHandler_erase P H eq draw heq] at hv
  split at hv
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hv
    rw [hv.2]
    exact Nat.le_succ _
  · simp only [support_map, Set.mem_image] at hv
    obtain ⟨r, _, hv⟩ := hv
    have := congrArg (fun p : val.Value base × List (key.Value base × val.Value base) => p.2.length) hv
    simp at this
    omega

/-- A cache procedure changes its returned list, not an unrelated ambient store. This
exact run law permits inlining it under a closed machine whose only used effect is sampling. -/
theorem cacheGet_run_state {S : Type} {Cmd' : Ty Atom → Ty Atom → Type}
    (P : Primitives base Op) (H : Handler base Cmd spec)
    (HS : HandlerM base Cmd' (StateT S (OracleComp spec)))
    (eq : Op (.pair key key) .bool) (draw : Cmd .unit val) (draw' : Cmd' .unit val)
    (hdraw : ∀ s, (HS draw' ()).run s = (fun r => (r, s)) <$> H draw ())
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base))
    (state : S) :
    ((cacheGet eq draw').run P HS (k, default, xs, ())).run state =
      (fun r => (r, state)) <$> (cacheGet eq draw).run P H (k, default, xs, ()) := by
  by_cases hb : ((lookup eq).run P (k, default, xs, ())).value.1 = true <;>
    simp [cacheGet, Program.run, Expr.run, Var.get, Var.depth, hb, hdraw, -Expr.run_value,
      StateT.run_map, bind_pure_comp]

end Signatures.Runtime
