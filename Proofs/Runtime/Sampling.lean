import Proofs.Runtime.Program
import VCVio.OracleComp.Constructions.SampleableType
import Mathlib.Data.List.Fold

/-! A compiled table-initialization loop. Each entry is an actual scalar-sampling command and
one list-cell allocation. No whole-table draw or assumed whole-sampler time bound is used.
The ordered variant has exactly the native vector sampler's list-valued behavior. -/

open OracleComp OracleSpec

namespace Signatures.Runtime

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}
  {cell : Ty Atom} {I : Type} {spec : OracleSpec I}

def drawAndCons (draw : Cmd .unit cell) : Program Op Cmd [.list cell, .nat] (.list cell) :=
  .bind (.query draw .unit) (.ret (.cons (.var .here) (.var (.there .here))))

/-- The input is the number of cells. The loop uses constant-time linked-list insertion. -/
def sampleList (draw : Cmd .unit cell) : Program Op Cmd [.nat] (.list cell) :=
  .loop (.var .here) .nil (drawAndCons draw)

theorem drawAndCons_denote (P : Primitives base Op) (H : Semantics base Cmd spec)
    (draw : Cmd .unit cell) (xs : List (cell.Value base)) (n : Nat) :
    (drawAndCons (Op := Op) draw).denote P H (xs, n, ()) =
      (fun x => x :: xs) <$> H draw () := by
  simp [drawAndCons, Program.denote, Expr.denote, Var.get, bind_pure_comp]

theorem sampleList_denote (P : Primitives base Op) (H : Semantics base Cmd spec)
    (draw : Cmd .unit cell) (n : Nat) :
    (sampleList (Op := Op) draw).denote P H (n, ()) =
      repeatDenote (fun xs => (fun x => x :: xs) <$> H draw ()) n [] := by
  simp only [sampleList, Program.denote, Expr.denote, Var.get]
  congr 1
  funext xs
  exact drawAndCons_denote P H draw xs n

theorem drawAndCons_steps_le (P : Primitives base Op) (H : Handler base Cmd spec)
    (draw : Cmd .unit cell) (c : Nat)
    (hdraw : ∀ r ∈ support (H draw ()), r.steps ≤ c)
    (xs : List (cell.Value base)) (n : Nat) (z : Run (List (cell.Value base)))
    (hz : z ∈ support ((drawAndCons (Op := Op) draw).run P H (xs, n, ()))) :
    z.steps ≤ c + 8 := by
  simp only [drawAndCons, Program.run, Expr.run, Var.get, Var.depth, pure_bind,
    bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  have := hdraw r hr
  dsimp
  omega

theorem sampleList_steps_le (P : Primitives base Op) (H : Handler base Cmd spec)
    (draw : Cmd .unit cell) (c : Nat)
    (hdraw : ∀ r ∈ support (H draw ()), r.steps ≤ c)
    (n : Nat) (z : Run (List (cell.Value base)))
    (hz : z ∈ support ((sampleList (Op := Op) draw).run P H (n, ()))) :
    z.steps ≤ n * (c + 10) + 4 := by
  simp only [sampleList, Program.run, Expr.run, Var.get, Var.depth,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  have h := repeatRun_steps_le
    (fun xs => (drawAndCons (Op := Op) draw).run P H (xs, n, ()))
    (c + 8) (fun xs z hz => drawAndCons_steps_le P H draw c hdraw xs n z hz) n [] r hr
  dsimp
  nlinarith

theorem repeatDenote_cons_length {α : Type} (draw : OracleComp spec α) (n : Nat)
    (xs ys : List α)
    (h : ys ∈ support (repeatDenote (fun xs => (fun x => x :: xs) <$> draw) n xs)) :
    ys.length = n + xs.length := by
  induction n generalizing xs ys with
  | zero => simpa [repeatDenote] using congrArg List.length (by simpa [repeatDenote] using h)
  | succ n ih =>
      simp only [repeatDenote, mem_support_bind_iff, support_map, Set.mem_image] at h
      obtain ⟨_, ⟨a, _, rfl⟩, h⟩ := h
      have := ih (a :: xs) ys h
      simp only [List.length_cons] at this
      omega

theorem sampleList_length (P : Primitives base Op) (H : Handler base Cmd spec)
    (draw : Cmd .unit cell) (n : Nat) (z : Run (List (cell.Value base)))
    (hz : z ∈ support ((sampleList (Op := Op) draw).run P H (n, ()))) :
    z.value.length = n := by
  have hv : z.value ∈ support ((sampleList (Op := Op) draw).denote P
      (fun instr x => Run.value <$> H instr x) (n, ())) := by
    rw [← Program.run_erase, support_map]
    exact ⟨z, hz, rfl⟩
  rw [sampleList_denote] at hv
  simpa using repeatDenote_cons_length (Run.value <$> H draw ()) n [] z.value hv

def reverseList {Γ : List (Ty Atom)} : Expr Op (.list cell :: Γ) (.list cell) :=
  .fold (.var .here) .nil (.cons (.var .here) (.var (.there .here)))

@[simp] theorem reverseList_denote (P : Primitives base Op) {Γ : List (Ty Atom)}
    (xs : List (cell.Value base)) (env : Env base Γ) :
    (reverseList (Op := Op)).denote P (xs, env) = xs.reverse := by
  simp [reverseList, Expr.denote, Var.get, ← Function.flip_def, List.foldl_cons_nil]

theorem reverseList_steps_le (P : Primitives base Op) {Γ : List (Ty Atom)}
    (xs : List (cell.Value base)) (env : Env base Γ) :
    ((reverseList (Op := Op)).run P (xs, env)).steps ≤ 7 * xs.length + 4 := by
  have h := foldRun_steps_le
    (fun (x : cell.Value base) (acc : List (cell.Value base)) =>
      (Expr.cons (.var .here) (.var (.there .here)) :
        Expr Op (cell :: .list cell :: .list cell :: Γ) (.list cell)).run P (x, acc, xs, env))
    4 (by intros; simp [Expr.run, Var.get, Var.depth]) xs []
  dsimp [Expr.run, Var.get, Var.depth] at h
  dsimp [reverseList, Expr.run, Var.get, Var.depth]
  nlinarith

def sampleTable (draw : Cmd .unit cell) : Program Op Cmd [.nat] (.list cell) :=
  .bind (sampleList draw) (.ret reverseList)

theorem sampleTable_denote (P : Primitives base Op) (H : Semantics base Cmd spec)
    (draw : Cmd .unit cell) (n : Nat) :
    (sampleTable (Op := Op) draw).denote P H (n, ()) =
      List.reverse <$> repeatDenote (fun xs => (fun x => x :: xs) <$> H draw ()) n [] := by
  simp only [sampleTable, Program.denote]
  simp_rw [reverseList_denote (Γ := [.nat]) P]
  rw [sampleList_denote P H draw n, bind_pure_comp]

theorem sampleTable_steps_le (P : Primitives base Op) (H : Handler base Cmd spec)
    (draw : Cmd .unit cell) (c : Nat)
    (hdraw : ∀ r ∈ support (H draw ()), r.steps ≤ c)
    (n : Nat) (z : Run (List (cell.Value base)))
    (hz : z ∈ support ((sampleTable (Op := Op) draw).run P H (n, ()))) :
    z.steps ≤ n * (c + 17) + 10 := by
  simp only [sampleTable, Program.run, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨r, hr, _, rfl, rfl⟩ := hz
  have hs := sampleList_steps_le P H draw c hdraw n r hr
  have hl := sampleList_length P H draw n r hr
  have hv := reverseList_steps_le (Γ := [.nat]) P r.value (n, ())
  dsimp
  nlinarith

theorem sampleTable_length (P : Primitives base Op) (H : Handler base Cmd spec)
    (draw : Cmd .unit cell) (n : Nat) (z : Run (List (cell.Value base)))
    (hz : z ∈ support ((sampleTable (Op := Op) draw).run P H (n, ()))) :
    z.value.length = n := by
  simp only [sampleTable, Program.run, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨r, hr, _, rfl, rfl⟩ := hz
  simpa only [Expr.run_value, reverseList_denote (cell := cell) (Γ := [.nat]) P,
    List.length_reverse] using
    sampleList_length P H draw n r hr

/-- The linked-list loop follows the native sampler's sequence of scalar draws. Reversing
its accumulator gives the same program, not merely the same output distribution. -/
theorem repeatDenote_cons_uniform (F : Type) [SampleableType F] (n : Nat) (xs : List F) :
    repeatDenote (fun ys => (fun x => x :: ys) <$> ($ᵗ F)) n xs =
      (fun v : Vector F n => v.toList.reverse ++ xs) <$> SampleableType.vector F n := by
  induction n with
  | zero => simp [repeatDenote, SampleableType.vector]
  | succ n ih =>
      rw [repeatDenote_succ_right, ih]
      simp [SampleableType.vector, seq_eq_bind_map, bind_map_left, map_bind, Vector.toList_push]

theorem sampleTable_uniform (P : Primitives base Op) (H : Semantics base Cmd unifSpec)
    [SampleableType (cell.Value base)] (draw : Cmd .unit cell)
    (hdraw : H draw () = $ᵗ cell.Value base) (n : Nat) :
    (sampleTable (Op := Op) draw).denote P H (n, ()) =
      Vector.toList <$> SampleableType.vector (cell.Value base) n := by
  rw [sampleTable_denote, hdraw, repeatDenote_cons_uniform]
  simp

end Signatures.Runtime
