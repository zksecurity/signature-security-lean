import Signatures.Runtime.EncodedReplay
import Signatures.Runtime.MixedReplay
import Signatures.Runtime.Sampling

/-! Charged full-list selection of a fork prefix. State contains the remaining live
ordinal, a found bit, its answer, the prefix length and the reversed prefix. -/

namespace Signatures.Runtime.Schnorr

abbrev scanState : Ty CryptoAtom :=
  .pair .nat (.pair .bool (.pair scalar (.pair .nat (.list Replay.Mixed.event))))

private def cell : Expr CryptoOp
    [Replay.Mixed.event, scanState, .nat, .list Replay.Mixed.event] Replay.Mixed.event := .var .here
private def acc : Expr CryptoOp
    [Replay.Mixed.event, scanState, .nat, .list Replay.Mixed.event] scanState := .var (.there .here)

private def scanKeep (remaining : Expr CryptoOp
    [Replay.Mixed.event, scanState, .nat, .list Replay.Mixed.event] .nat) :
    Expr CryptoOp [Replay.Mixed.event, scanState, .nat, .list Replay.Mixed.event] scanState :=
  .pair remaining (.pair (.bool false) (.pair (.fst (.snd (.snd acc)))
    (.pair (.op .natAdd (.pair (.fst (.snd (.snd (.snd acc)))) (.nat 1)))
      (.cons cell (.snd (.snd (.snd (.snd acc))))))))

def scanBody : Expr CryptoOp
    [Replay.Mixed.event, scanState, .nat, .list Replay.Mixed.event] scanState :=
  .branch (.fst (.snd acc)) acc
    (.branch (.op .natEq (.pair (.fst cell) (.nat 1)))
      (.branch (.op .natEq (.pair (.fst acc) (.nat 0)))
        (.pair (.nat 0) (.pair (.bool true) (.pair (.fst (.snd cell)) (.snd (.snd (.snd acc))))))
        (scanKeep (.op .natSub (.pair (.fst acc) (.nat 1)))))
      (scanKeep (.fst acc)))

def scanFold : Expr CryptoOp [.nat, .list Replay.Mixed.event] scanState :=
  .fold (.var (.there .here))
    (.pair (.var .here) (.pair (.bool false) (.pair (.op .zero .unit) (.pair (.nat 0) .nil))))
    scanBody

def scanStep {F : Type} (s : Nat × Bool × F × Nat × List (TapeCell F))
    (x : TapeCell F) : Nat × Bool × F × Nat × List (TapeCell F) :=
  if s.2.1 then s
  else if x.1 = 1 then
    if s.1 = 0 then (0, true, x.2.1, s.2.2.2)
    else (s.1 - 1, false, s.2.2.1, s.2.2.2.1 + 1, x :: s.2.2.2.2)
  else (s.1, false, s.2.2.1, s.2.2.2.1 + 1, x :: s.2.2.2.2)

variable {F G₁ G₂ K M : Type} [Field F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem scanBody_denote (cost : PrimitiveCosts) (x : TapeCell F)
    (s : Nat × Bool × F × Nat × List (TapeCell F)) (n : Nat) (xs : List (TapeCell F)) :
    scanBody.denote (arithmetic F G₁ G₂ K M cost) (x, s, n, xs, ()) = scanStep s x := by
  rcases s with ⟨remaining, found, answer, size, prior⟩
  cases found <;> by_cases hx : x.1 = 1 <;> by_cases hn : remaining = 0 <;>
    simp [scanBody, scanKeep, scanStep, cell, acc, Expr.denote, Var.get,
      arithmetic, hx, hn]

theorem scanFold_denote (cost : PrimitiveCosts) (n : Nat) (xs : List (TapeCell F)) :
    scanFold.denote (arithmetic F G₁ G₂ K M cost) (n, xs, ()) =
      xs.foldl scanStep (n, false, (0 : F), 0, []) := by
  change xs.foldl (fun s x => scanBody.denote (arithmetic F G₁ G₂ K M cost)
    (x, s, n, xs, ())) (n, false, (0 : F), 0, []) = _
  simp_rw [scanBody_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]

theorem scanBody_steps (cost : PrimitiveCosts) (x : TapeCell F)
    (s : Nat × Bool × F × Nat × List (TapeCell F)) (n : Nat) (xs : List (TapeCell F)) :
    (scanBody.run (arithmetic F G₁ G₂ K M cost) (x, s, n, xs, ())).steps ≤
      4 * cost.natOp + 60 := by
  rcases s with ⟨remaining, found, answer, size, prior⟩
  cases found <;> by_cases hx : x.1 = 1 <;> by_cases hn : remaining = 0 <;>
    simp [scanBody, scanKeep, cell, acc, Expr.run, Var.get, Var.depth,
      arithmetic, CryptoOp.price, hx, hn] <;> omega

theorem scanFold_steps (cost : PrimitiveCosts) (n : Nat) (xs : List (TapeCell F)) :
    (scanFold.run (arithmetic F G₁ G₂ K M cost) (n, xs, ())).steps ≤
      xs.length * (4 * cost.natOp + 63) + cost.field + 14 := by
  have h := foldRun_steps_le
    (fun x s => scanBody.run (arithmetic F G₁ G₂ K M cost) (x, s, n, xs, ()))
    (4 * cost.natOp + 60) (fun x s => scanBody_steps cost x s n xs)
    xs (n, false, (0 : F), 0, [])
  dsimp [scanFold, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price] at h ⊢
  nlinarith

omit [Field F] [DecidableEq F] in
theorem scanStep_found (xs : List (TapeCell F)) (n : Nat) (answer : F)
    (size : Nat) (prior : List (TapeCell F)) :
    xs.foldl scanStep (n, true, answer, size, prior) = (n, true, answer, size, prior) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [scanStep] using ih

omit [Field F] [DecidableEq F] in
theorem scanStep_size (xs : List (TapeCell F))
    (s : Nat × Bool × F × Nat × List (TapeCell F))
    (hs : s.2.2.2.1 = s.2.2.2.2.length) :
    (xs.foldl scanStep s).2.2.2.1 = (xs.foldl scanStep s).2.2.2.2.length ∧
      (xs.foldl scanStep s).2.2.2.1 ≤ s.2.2.2.1 + xs.length := by
  induction xs generalizing s with
  | nil => exact ⟨hs, le_rfl⟩
  | cons x xs ih =>
    have ht : (scanStep s x).2.2.2.1 = (scanStep s x).2.2.2.2.length ∧
        (scanStep s x).2.2.2.1 ≤ s.2.2.2.1 + 1 := by
      unfold scanStep
      split <;> (try split) <;> (try split) <;> simp_all
    have h := ih (scanStep s x) ht.1
    refine ⟨h.1, ?_⟩
    simp only [List.foldl_cons, List.length_cons]
    omega

def scanView {F : Type} (s : Nat × Bool × F × Nat × List (TapeCell F)) :
    Option (List (TapeCell F) × F) :=
  if s.2.1 then some (s.2.2.2.2.reverse, s.2.2.1) else none

omit [Field F] [DecidableEq F] in
theorem scanStep_view (xs : List (TapeCell F)) (n : Nat) (answer : F)
    (size : Nat) (prior : List (TapeCell F)) :
    scanView (xs.foldl scanStep (n, false, answer, size, prior)) =
      (splitCells n xs).map (fun p => (prior.reverse ++ p.1, p.2)) := by
  induction xs generalizing n answer size prior with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x.1 = 1
    · cases n with
      | zero => simp [scanStep, splitCells, hx, scanStep_found, scanView]
      | succ n =>
        simp only [List.foldl_cons, scanStep, Bool.false_eq_true, ite_false, hx, ite_true,
          Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, Nat.add_sub_cancel]
        rw [ih]
        simp [splitCells, hx, List.reverse_cons, List.append_assoc, Option.map_map,
          Function.comp_def]
    · simp only [List.foldl_cons, scanStep, Bool.false_eq_true, ite_false, hx]
      rw [ih]
      simp [splitCells, hx, List.reverse_cons, List.append_assoc, Option.map_map,
        Function.comp_def]

theorem scanFold_view (cost : PrimitiveCosts) (n : Nat) (xs : List (TapeCell F)) :
    scanView ((scanFold.run (arithmetic F G₁ G₂ K M cost) (n, xs, ())).value) =
      splitCells n xs := by
  rw [Expr.run_value, scanFold_denote]
  simpa using scanStep_view xs n (0 : F) 0 []

abbrev scanResult : Ty CryptoAtom :=
  .pair .bool (.pair scalar (.pair .nat (.list Replay.Mixed.event)))

private def scanReverse : Expr CryptoOp [scanState, .nat, .list Replay.Mixed.event]
    (.list Replay.Mixed.event) :=
  .letE (.snd (.snd (.snd (.snd (.var .here))))) reverseList

/-- Return the found bit, old answer, prefix length and chronological prefix. -/
def scanCode : Expr CryptoOp [.nat, .list Replay.Mixed.event] scanResult :=
  .letE scanFold (.pair (.fst (.snd (.var .here)))
    (.pair (.fst (.snd (.snd (.var .here))))
      (.pair (.fst (.snd (.snd (.snd (.var .here))))) scanReverse)))

theorem scanCode_denote (cost : PrimitiveCosts) (n : Nat) (xs : List (TapeCell F)) :
    scanCode.denote (arithmetic F G₁ G₂ K M cost) (n, xs, ()) =
      let s := xs.foldl scanStep (n, false, (0 : F), 0, [])
      (s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.reverse) := by
  simp only [scanCode, Expr.denote, Var.get, scanReverse]
  rw [reverseList_denote]
  rw [scanFold_denote]

theorem scanCode_steps (cost : PrimitiveCosts) (n : Nat) (xs : List (TapeCell F)) :
    (scanCode.run (arithmetic F G₁ G₂ K M cost) (n, xs, ())).steps ≤
      xs.length * (4 * cost.natOp + 70) + cost.field + 40 := by
  let s := (scanFold.run (arithmetic F G₁ G₂ K M cost) (n, xs, ())).value
  have hs : s = xs.foldl scanStep (n, false, (0 : F), 0, []) := by
    exact (Expr.run_value _ _ _).trans (scanFold_denote cost n xs)
  have hf := scanFold_steps (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost n xs
  have hl := scanStep_size xs (n, false, (0 : F), 0, []) rfl
  have hr := reverseList_steps_le (cell := Replay.Mixed.event)
    (Γ := [scanState, .nat, .list Replay.Mixed.event]) (arithmetic F G₁ G₂ K M cost)
    s.2.2.2.2 (s, n, xs, ())
  have hlen : s.2.2.2.2.length ≤ xs.length := by
    rw [hs, ← hl.1]
    simpa only [Nat.zero_add] using hl.2
  dsimp only [scanCode, Expr.run, Var.get, Var.depth, scanReverse]
  change _ + (_ + (_ + (_ + (5 + _ + 1) + 1) + 1) + 1) + 1 ≤ _
  nlinarith

end Signatures.Runtime.Schnorr
